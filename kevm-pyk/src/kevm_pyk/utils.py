from logging import Logger
from typing import Collection, Iterable, List, Optional, Tuple

from pyk.cterm import CTerm
from pyk.kast import (
    KApply,
    KClaim,
    KDefinition,
    KFlatModule,
    KImport,
    KInner,
    KNonTerminal,
    KRewrite,
    KRule,
    KToken,
    KVariable,
    Subst,
    build_assoc,
)
from pyk.kastManip import (
    abstract_term_safely,
    bool_to_ml_pred,
    bottom_up,
    extract_lhs,
    extract_rhs,
    flatten_label,
    free_vars,
    get_cell,
    is_anon_var,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    split_config_and_constraints,
    split_config_from,
    substitute,
    undo_aliases,
)
from pyk.kcfg import KCFG
from pyk.ktool import KPrint, KProve
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kbool import FALSE
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlAnd, mlTop


def simplify_int(i_exp: KInner) -> KInner:
    accumulated = 0
    rest = []
    for i in flatten_label('_+Int_', i_exp):
        if type(i) is KToken:
            accumulated += int(i.token)
        else:
            rest.append(i)
    new_int = build_assoc(intToken(0), '_+Int_', [intToken(accumulated)] + rest)
    return new_int


def instantiate_cell_vars(definition: KDefinition, term: KInner) -> KInner:
    def _cell_vars_to_labels(_kast: KInner) -> KInner:
        if type(_kast) is KApply and _kast.is_cell:
            production = definition.production_for_klabel(_kast.label)
            production_arity = [prod_item.sort for prod_item in production.items if type(prod_item) is KNonTerminal]
            new_args = []
            for sort, arg in zip(production_arity, _kast.args):
                if sort.name.endswith('Cell') and type(arg) is KVariable:
                    new_args.append(definition.empty_config(sort))
                else:
                    new_args.append(arg)
            return KApply(_kast.label, new_args)
        return _kast

    return bottom_up(_cell_vars_to_labels, term)


def KDefinition__crewrites(defn: KDefinition) -> List[Tuple[int, CTerm, CTerm]]:  # noqa: N802
    rules = KDefinition__semantic_rules(defn)
    crewrites = []
    for rule in rules:
        rule_body = instantiate_cell_vars(defn, rule.body)
        # TODO: We have to use remove_generated_cells because KCFG.create_node does so.
        rule_lhs = remove_generated_cells(extract_lhs(rule_body))
        rule_rhs = remove_generated_cells(extract_rhs(rule_body))
        priority = 50
        if 'priority' in rule.att:
            priority = int(rule.att['priority'])
        crewrite = (
            priority,
            CTerm(mlAnd([rule_lhs, bool_to_ml_pred(rule.requires)])),
            CTerm(mlAnd([rule_rhs, bool_to_ml_pred(rule.ensures)])),
        )
        crewrites.append(crewrite)
    return crewrites


# TODO: Needs to be reviewed for accuracy
def KDefinition__semantic_rules(_self: KDefinition) -> List[KRule]:  # noqa: N802
    _semantic_rules = []
    for r in _self.rules:
        if type(r.body) is KApply and r.body.label.name == '<generatedTop>':
            _semantic_rules.append(r)
        elif type(r.body) is KRewrite and type(r.body.lhs) is KApply and r.body.lhs.label.name == '<generatedTop>':
            _semantic_rules.append(r)
    return _semantic_rules


def KCFG__replace_node(cfg: KCFG, node_id: str, new_cterm: CTerm) -> KCFG:  # noqa: N802

    # Remove old node, record data
    node = cfg.node(node_id)
    in_edges = cfg.edges(target_id=node.id)
    out_edges = cfg.edges(source_id=node.id)
    in_covers = cfg.covers(target_id=node.id)
    out_covers = cfg.covers(source_id=node.id)
    init = cfg.is_init(node.id)
    target = cfg.is_target(node.id)
    expanded = cfg.is_expanded(node.id)
    in_expanded = {edge.source.id: cfg.is_expanded(edge.source.id) for edge in in_edges}
    cfg.remove_node(node.id)

    # Add the new, update data
    new_node = cfg.get_or_create_node(new_cterm)
    for in_edge in in_edges:
        cfg.create_edge(in_edge.source.id, new_node.id, in_edge.condition, in_edge.depth)
    for out_edge in out_edges:
        cfg.create_edge(new_node.id, out_edge.target.id, out_edge.condition, out_edge.depth)
    for in_cover in in_covers:
        cfg.create_cover(in_cover.source.id, new_node.id)
    for out_cover in out_covers:
        cfg.create_cover(new_node.id, out_cover.target.id)
    if init:
        cfg.add_init(new_node.id)
    if target:
        cfg.add_target(new_node.id)
    if expanded:
        cfg.add_expanded(new_node.id)
    for nid in in_expanded:
        if in_expanded[nid]:
            cfg.add_expanded(nid)

    return cfg


def KProve_prove_claim(  # noqa: N802
    kprove: KProve,
    claim: KClaim,
    claim_id: str,
    logger: Logger,
    depth: Optional[int] = None,
    lemmas: Iterable[KRule] = (),
    smt: bool = True,
) -> Tuple[bool, KInner]:
    logger.info(f'Proving claim: {claim_id}')
    prove_args = []
    if depth is not None:
        prove_args += ['--depth', str(depth)]
    if not smt:
        prove_args += ['--smt', 'none']
    result = kprove.prove_claim(claim, claim_id, args=prove_args, lemmas=lemmas)
    failed = False
    if type(result) is KApply and result.label.name == '#Top':
        logger.info(f'Proved claim: {claim_id}')
    else:
        logger.error(f'Failed to prove claim: {claim_id}')
        failed = True
    return failed, result


def KPrint_make_unparsing(_self: KPrint, extra_modules: Iterable[KFlatModule] = ()) -> KPrint:  # noqa: N802
    modules = _self.definition.modules + tuple(extra_modules)
    main_module = KFlatModule('UNPARSING', [], [KImport(_m.name) for _m in modules])
    defn = KDefinition('UNPARSING', (main_module,) + modules)
    kprint = KPrint(_self.definition_dir)
    kprint._definition = defn
    kprint._symbol_table = None
    return kprint


def add_include_arg(includes: Iterable[str]) -> List[str]:
    return [arg for include in includes for arg in ['-I', include]]


def abstract_cell_vars(cterm: KInner, keep_vars: Collection[KVariable] = ()) -> KInner:
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return substitute(config, subst)


def sanitize_config(defn: KDefinition, init_term: KInner) -> KInner:
    def _var_name(vname: str) -> str:
        new_vname = vname
        while new_vname.startswith('_') or new_vname.startswith('?'):
            new_vname = new_vname[1:]
        return new_vname

    free_vars_subst = {vname: KVariable(_var_name(vname)) for vname in free_vars(init_term)}

    # TODO: This is somewhat hacky. We shouldn't have to touch the config this much.
    # Likely, the frontend should just be giving us initial states with these already in place.
    def _remove_cell_map_definedness(_kast: KInner) -> KInner:
        if type(_kast) is KApply:
            if _kast.label.name.endswith('CellMap:in_keys'):
                return FALSE
            elif _kast.label.name.endswith('CellMapItem'):
                return _kast.args[1]
        return _kast

    new_term = substitute(init_term, free_vars_subst)
    new_term = remove_generated_cells(new_term)
    new_term = bottom_up(_remove_cell_map_definedness, new_term)

    if not (type(new_term) is KApply and new_term.label.name in ['#Top', '#Bottom']):
        config, constraint = split_config_and_constraints(new_term)
        constraints = [bool_to_ml_pred(ml_pred_to_bool(c, unsafe=True)) for c in flatten_label('#And', constraint)]
        new_term = mlAnd([config] + constraints)
        new_term = undo_aliases(defn, new_term)

    return new_term


def check_implication(kprint: KPrint, concrete: CTerm, abstract: CTerm) -> Tuple[bool, str]:
    def _is_cell_subst(csubst: KInner) -> bool:
        if type(csubst) is KApply and csubst.label.name == '_==K_':
            csubst_arg = csubst.args[0]
            if type(csubst_arg) is KVariable and csubst_arg.name.endswith('_CELL'):
                return True
        return False

    def _is_negative_cell_subst(constraint: KInner) -> bool:
        constraint_bool = ml_pred_to_bool(constraint)
        if type(constraint_bool) is KApply and constraint_bool.label.name == 'notBool_':
            negative_constraint = constraint_bool.args[0]
            if type(negative_constraint) is KApply and negative_constraint.label.name == '_andBool_':
                constraints = flatten_label('_andBool_', negative_constraint)
                cell_constraints = list(filter(_is_cell_subst, constraints))
                if len(cell_constraints) > 0:
                    return True
        return False

    concrete_config, *concrete_constraints = concrete
    abstract_config, *abstract_constraints = abstract
    config_match = abstract_config.match(concrete_config)
    minimized_rewrite_str = kprint.pretty_print(
        minimize_term(push_down_rewrites(KRewrite(concrete_config, abstract_config)))
    )
    if config_match is None:
        _, concrete_subst = split_config_from(concrete_config)
        cell_names = concrete_subst.keys()
        failing_cells = []
        combined_subst = Subst()
        for cell in cell_names:
            concrete_cell = get_cell(concrete_config, cell)
            abstract_cell = get_cell(abstract_config, cell)
            cell_match = abstract_cell.match(concrete_cell)
            if cell_match is None or combined_subst.union(cell_match) is None:
                failing_cell = push_down_rewrites(KRewrite(concrete_cell, abstract_cell))
                failing_cell = no_cell_rewrite_to_dots(failing_cell)
                failing_cells.append((cell, failing_cell))
            else:
                new_subst = combined_subst.union(cell_match)
                assert new_subst is not None
                combined_subst = new_subst
                abstract_config = cell_match.apply(abstract_config)
        failing_cells_str = '\n'.join(
            f'{cell}: {kprint.pretty_print(minimize_term(rew))}' for cell, rew in failing_cells
        )
        return (
            False,
            f'Structural matching failed (concrete => abstract):\n{minimized_rewrite_str}\n\nThe following cells failed individually (concrete => abstract):\n{failing_cells_str}',
        )
    else:
        abstract_constraints = [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints]
        abstract_constraints = list(
            filter(
                lambda x: not CTerm._is_spurious_constraint(x),
                [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints],
            )
        )
        impl = CTerm._ml_impl(concrete_constraints, abstract_constraints)
        if impl != mlTop(GENERATED_TOP_CELL):
            fail_str = kprint.pretty_print(impl)
            negative_cell_constraints = list(filter(_is_negative_cell_subst, concrete_constraints))
            if len(negative_cell_constraints) > 0:
                fail_str = f'{fail_str}\n\nNegated cell substitutions found (consider using _ => ?_):\n' + '\n'.join(
                    [kprint.pretty_print(cc) for cc in negative_cell_constraints]
                )
            return (False, f'Implication check failed, the following is the remaining implication:\n{fail_str}')
    return (True, '')


def no_cell_rewrite_to_dots(term: KInner) -> KInner:
    def _no_cell_rewrite_to_dots(_term: KInner) -> KInner:
        if type(_term) is KApply and _term.is_cell:
            lhs = extract_lhs(_term)
            rhs = extract_rhs(_term)
            if lhs == rhs:
                return KApply(_term.label, [abstract_term_safely(lhs, base_name=_term.label.name)])
        return _term

    return bottom_up(_no_cell_rewrite_to_dots, term)
