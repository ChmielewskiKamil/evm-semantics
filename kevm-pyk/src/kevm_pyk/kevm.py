import hashlib
import json
import logging
import sys
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, Iterable, List, Optional, Tuple

from pyk.cli_utils import run_process
from pyk.cterm import CTerm
from pyk.kast import KApply, KAst, KInner, KLabel, KSequence, KSort, KToken, KVariable, Subst, build_assoc, build_cons
from pyk.kastManip import flatten_label, get_cell, split_config_from
from pyk.ktool import KProve, KRun
from pyk.ktool.kompile import KompileBackend
from pyk.ktool.kprint import paren
from pyk.prelude.kbool import FALSE, andBool, notBool, orBool
from pyk.prelude.kint import intToken, ltInt
from pyk.prelude.ml import is_bottom, mlAnd, mlBottom, mlEqualsTrue, mlTop
from pyk.prelude.string import stringToken
from pyk.utils import unique

from .utils import KDefinition__crewrites, add_include_arg, simplify_int

_LOGGER: Final = logging.getLogger(__name__)


# KEVM class


class KEVM(KProve, KRun):
    _crewrites: Optional[List[Tuple[int, CTerm, CTerm]]]
    _crewrites_file: Path
    _rule_index: Optional[Dict[str, List[Tuple[int, CTerm, CTerm]]]]
    _opcode_lookup: Dict[Tuple[KInner, KInner], Dict[KInner, Tuple[KInner, int]]]
    _current_schedule: Optional[KInner]

    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        profile: bool = False,
    ) -> None:
        # I'm going for the simplest version here, we can change later if there is an advantage.
        # https://stackoverflow.com/questions/9575409/calling-parent-class-init-with-multiple-inheritance-whats-the-right-way
        # Note that they say using `super` supports dependency injection, but I have never liked dependency injection anyway.
        KProve.__init__(self, definition_dir, use_directory=use_directory, main_file=main_file, profile=profile)
        KRun.__init__(self, definition_dir, use_directory=use_directory, profile=profile)
        KEVM._patch_symbol_table(self.symbol_table)
        self._crewrites = None
        self._crewrites_file = self.definition_dir / 'crewrites.json'
        self._rule_index = None
        self._opcode_lookup = {}
        self._current_schedule = None

    @property
    def crewrites(self) -> List[Tuple[int, CTerm, CTerm]]:
        if not self._crewrites:
            if self._crewrites_file.exists():
                _crewrites: List[Tuple[int, CTerm, CTerm]] = []
                with open(self._crewrites_file, 'r') as crf:
                    for cr in json.loads(crf.read()):
                        priority, lhs_json, rhs_json = cr
                        lhs_kast = KAst.from_dict(lhs_json)
                        rhs_kast = KAst.from_dict(rhs_json)
                        assert type(priority) is int
                        assert isinstance(lhs_kast, KInner)
                        assert isinstance(rhs_kast, KInner)
                        _crewrites.append((priority, CTerm(lhs_kast), CTerm(rhs_kast)))
                self._crewrites = _crewrites
                _LOGGER.info(f'Loaded crewrites: {self._crewrites_file}')
            else:
                _LOGGER.info('Computing crewrites.')
                self._crewrites = KDefinition__crewrites(self.definition)
                with open(self._crewrites_file, 'w') as crf:
                    json_crewrites = []
                    for priority, lhs, rhs in self._crewrites:
                        json_crewrite = [priority, lhs.kast.to_dict(), rhs.kast.to_dict()]
                        json_crewrites.append(json_crewrite)
                    crf.write(json.dumps(json_crewrites))
                    _LOGGER.info(f'Recorded crewrites: {self._crewrites_file}')
        return self._crewrites

    def compute_rule_index(self) -> None:
        self._rule_index = {}
        self.crewrites
        _LOGGER.info('Computing rule index.')
        for priority, lhs, rhs in self.crewrites:
            index = KEVM.rule_index(lhs)
            if index is not None:
                if index not in self._rule_index:
                    self._rule_index[index] = []
                self._rule_index[index].append((priority, lhs, rhs))

    @staticmethod
    def rule_index(cterm: CTerm) -> Optional[str]:
        k_cell = get_cell(cterm.config, 'K_CELL')
        if type(k_cell) is KSequence and k_cell.arity > 0 and type(k_cell.items[0]) is KApply:
            return k_cell.items[0].label.name
        return None

    def indexed_rules(self, cterm: CTerm) -> List[Tuple[int, CTerm, CTerm]]:
        if not self._rule_index:
            self.compute_rule_index()
        if self._rule_index:
            index = KEVM.rule_index(cterm)
            if index is not None and index in self._rule_index:
                rules = self._rule_index[index]
                _LOGGER.info(f'Rules found for index {index}: {len(rules)}')
                return rules
        k_cell_compact = ' '.join(self.pretty_print(get_cell(cterm.config, "K_CELL")).split("\n"))
        _LOGGER.info(f'No rules in index for: {k_cell_compact}')
        return self.crewrites

    @staticmethod
    def opcode_map_to_dict(map: KInner) -> Dict[KInner, Tuple[KInner, int]]:
        _dict = {}
        for map_item in flatten_label('_Map_', map):
            assert type(map_item) is KApply
            assert map_item.label.name == '_|->_'
            pcount = map_item.args[0]
            opcode = map_item.args[1]
            assert type(opcode) is KApply and opcode.label.name == 'opcode(_,_)_FOUNDRY_OpCodeResult_OpCode_Int'
            opcode_val = opcode.args[0]
            opcode_width = opcode.args[1]
            assert type(opcode_width) is KToken
            _dict[pcount] = (opcode_val, int(opcode_width.token))
        return _dict

    def add_opcode_table(self, program: KInner, schedule: KInner) -> None:
        if (program, schedule) not in self._opcode_lookup:
            opcode_table_digest = hashlib.md5(
                (json.dumps(program.to_dict()) + json.dumps(schedule.to_dict())).encode('utf-8')
            ).hexdigest()
            opcode_table_file = self.use_directory / f'{opcode_table_digest}.json'
            if opcode_table_file.exists():
                pdict = {}
                with open(opcode_table_file, 'r') as phf:
                    for _pc, _op, width in json.loads(phf.read()):
                        op = KAst.from_dict(_op)
                        assert isinstance(op, KInner)
                        pc = KAst.from_dict(_pc)
                        assert isinstance(pc, KInner)
                        assert type(width) is int
                        pdict[pc] = (op, width)
                self._opcode_lookup[(program, schedule)] = pdict
                _LOGGER.info(
                    f'Loaded bytecode disassembly for {(self.pretty_print(program), self.pretty_print(schedule))} from: {opcode_table_file}'
                )

            else:
                _LOGGER.info(
                    f'Computing bytecode disassembly: {(self.pretty_print(program), self.pretty_print(schedule))}'
                )
                lookup_evm_pgm = KApply(
                    'dasm_program___FOUNDRY_EthereumSimulation_ByteArray_Schedule', [program, schedule]
                )
                run_args = [
                    "-cSCHEDULE=LblLONDON'Unds'EVM{}()",
                    '-pSCHEDULE=cat',
                    '-cMODE=LblNORMAL{}()',
                    '-pMODE=cat',
                    '-cCHAINID=\\dv{SortInt{}}("1")',
                    '-pCHAINID=cat',
                    '--no-expand-macros',
                ]
                result = self.run(lookup_evm_pgm, args=run_args)
                k_cell = get_cell(result.config, 'K_CELL')
                if type(k_cell) is KSequence and k_cell.arity > 0:
                    k_cell = k_cell.items[0]
                if type(k_cell) is KApply and k_cell.label.name == 'dasm_result__FOUNDRY_EthereumSimulation_Map':
                    self._opcode_lookup[(program, schedule)] = KEVM.opcode_map_to_dict(k_cell.args[0])

                with open(opcode_table_file, 'w') as phf:
                    json_program_lookup = []
                    for pc, (op, width) in self._opcode_lookup[(program, schedule)].items():
                        json_program_lookup.append([pc.to_dict(), op.to_dict(), width])
                    phf.write(json.dumps(json_program_lookup))
                    _LOGGER.info(
                        f'Recorded bytecode disassembly for {(self.pretty_print(program), self.pretty_print(schedule))} at: {opcode_table_file}'
                    )

    def opcode_lookup(
        self, program: KInner, pcount: KInner, schedule: KInner, compute: bool = False
    ) -> Optional[Tuple[KInner, int]]:
        if compute:
            self.add_opcode_table(program, schedule)

        if (program, schedule) in self._opcode_lookup and pcount in self._opcode_lookup[(program, schedule)]:
            return self._opcode_lookup[(program, schedule)][pcount]

        return None

    def simplify_int(self, i: KInner) -> KInner:
        if type(i) is KVariable or type(i) is KToken:
            return i

        i = simplify_int(i)

        gas_pattern = KApply('_-Int_', [KEVM.inf_gas(KVariable('V1')), KVariable('V2')])
        if gp_match := gas_pattern.match(i):
            i = KEVM.inf_gas(KApply('_-Int_', [gp_match['V1'], gp_match['V2']]))

        widthop_pattern = KApply('#widthOp(_)_EVM_Int_OpCode', [KVariable('OP')])
        new_is: List[KInner] = []
        for j in flatten_label('_+Int_', i):
            if op_match := widthop_pattern.match(j):
                new_is.append(intToken(KEVM.width_op(op_match['OP'])))
            else:
                new_is.append(j)
        i = build_assoc(intToken(0), '_+Int_', new_is)

        return i

    def simplify_constraint(self, constraint: KInner) -> KInner:

        if constraint == mlEqualsTrue(FALSE):
            return mlBottom()

        # { true #Equals ( notBool ( false andBool _ ) ) }
        # { true #Equals notBool ( false ) }
        trivial_pattern = mlEqualsTrue(notBool(andBool([FALSE, KVariable('_')])))
        if trivial_pattern.match(constraint):
            return mlTop()
        trivial_pattern = mlEqualsTrue(notBool(FALSE))
        if trivial_pattern.match(constraint):
            return mlTop()

        # { true #Equals V1 <=Int #gas(V2) }
        # { true #Equals #gas(V1) <Int V2 }
        # { true #Equals #gas(V1) >=Int V2 }
        inf_gas_pattern_1 = mlEqualsTrue(KApply('_<=Int_', [KVariable('V1'), KEVM.inf_gas(KVariable('V2'))]))
        if inf_gas_pattern_1.match(constraint):
            return mlTop()
        inf_gas_pattern_2 = mlEqualsTrue(KApply('_<Int_', [KEVM.inf_gas(KVariable('V1')), KVariable('V2')]))
        if inf_gas_pattern_2.match(constraint):
            return mlBottom()
        inf_gas_pattern_3 = mlEqualsTrue(KApply('_>=Int_', [KEVM.inf_gas(KVariable('V1')), KVariable('V2')]))
        if inf_gas_pattern_3.match(constraint):
            return mlTop()

        # { true #Equals #sizeWordStack(WS) <=Int 1024 }
        word_stack_size_pattern = mlEqualsTrue(
            KApply('_<=Int_', [KApply('#sizeWordStack(_)_EVM-TYPES_Int_WordStack', [KVariable('WS')]), intToken(1024)])
        )
        if ws_match := word_stack_size_pattern.match(constraint):
            wsitems = KEVM.wordstack_items(ws_match['WS'])
            if len(wsitems) > 0 and wsitems[-1] == KEVM.wordstack_empty():
                ws_len = len(wsitems) - 1
                return mlTop() if ws_len <= 1024 else mlBottom()

        # { true #Equals #stackOverflow(WS, OP) }
        # { true #Equals #stackUnderflow(WS, OP) }
        # { true #Equals notBool (#stackUnderflow(WS, OP) orBool #stackOverflow(WS, OP)) }
        stack_overflow_pattern = KApply(
            '#stackOverflow(_,_)_EVM_Bool_WordStack_OpCode', [KVariable('WS'), KVariable('OP')]
        )
        stack_underflow_pattern = KApply(
            '#stackUnderflow(_,_)_EVM_Bool_WordStack_OpCode', [KVariable('WS'), KVariable('OP')]
        )
        stack_overflow_constraint_pattern = mlEqualsTrue(stack_overflow_pattern)
        if socp_match := stack_overflow_constraint_pattern.match(constraint):
            wsitems = KEVM.wordstack_items(socp_match['WS'])
            if len(wsitems) > 0 and wsitems[-1] == KEVM.wordstack_empty():
                ws_len = len(wsitems) - 1
                if ws_len < 1024:
                    return mlBottom()
        stack_underflow_constraint_pattern = mlEqualsTrue(stack_underflow_pattern)
        if socp_match := stack_underflow_constraint_pattern.match(constraint):
            wsitems = KEVM.wordstack_items(socp_match['WS'])
            if len(wsitems) > 0 and wsitems[-1] == KEVM.wordstack_empty():
                ws_len = len(wsitems) - 1
                stack_needed = KEVM.stack_needed(socp_match['OP'])
                if stack_needed is not None and stack_needed <= ws_len:
                    return mlBottom()
        stack_fine_constraint_pattern = mlEqualsTrue(
            notBool(orBool([stack_underflow_constraint_pattern, stack_overflow_constraint_pattern]))
        )
        if sfcp_match := stack_fine_constraint_pattern.match(constraint):
            wsitems = KEVM.wordstack_items(sfcp_match['WS'])
            if len(wsitems) > 0 and wsitems[-1] == KEVM.wordstack_empty():
                ws_len = len(wsitems) - 1
                stack_needed = KEVM.stack_needed(sfcp_match['OP'])
                if ws_len < 1024 and stack_needed is not None and stack_needed <= ws_len:
                    return mlTop()

        # { true #Equals V1 +Int #widthOp(OP) >=Int V2 }
        # { true #Equals V1 +Int #widthOp(OP) <Int V2 }
        widthop_pattern = KApply('_+Int_', [KVariable('V1'), KApply('#widthOp(_)_EVM_Int_OpCode', [KVariable('OP')])])
        compact_widthop_pattern_1 = mlEqualsTrue(KApply('_>=Int_', [widthop_pattern, KVariable('V2')]))
        if cwop_match := compact_widthop_pattern_1.match(constraint):
            num = cwop_match['V1']
            if type(num) is KToken:
                new_width = int(num.token) + KEVM.width_op(cwop_match['OP'])
                constraint = mlEqualsTrue(KApply('_>=Int_', [intToken(new_width), cwop_match['V2']]))
        compact_widthop_pattern_2 = mlEqualsTrue(KApply('_<Int_', [widthop_pattern, KVariable('V2')]))
        if cwop_match := compact_widthop_pattern_2.match(constraint):
            num = cwop_match['V1']
            if type(num) is KToken:
                new_width = int(num.token) + KEVM.width_op(cwop_match['OP'])
                constraint = mlEqualsTrue(KApply('_<Int_', [intToken(new_width), cwop_match['V2']]))

        # { true #Equals V1 >=Int #sizeByteArray(V2) }
        concrete_bytearray_size_pattern = mlEqualsTrue(
            KApply('_>=Int_', [KVariable('V1'), KEVM.size_bytearray(KVariable('V2'))])
        )
        if cbsp_match := concrete_bytearray_size_pattern.match(constraint):
            new_i = simplify_int(cbsp_match['V1'])
            if self._current_schedule and self.opcode_lookup(cbsp_match['V2'], new_i, self._current_schedule):
                return mlBottom()
            return mlEqualsTrue(KApply('_>=Int_', [new_i, KEVM.size_bytearray(cbsp_match['V2'])]))

        # { true #Equals V1 <Int #sizeByteArray(V2) }
        concrete_bytearray_size_pattern = mlEqualsTrue(
            KApply('_<Int_', [KVariable('V1'), KEVM.size_bytearray(KVariable('V2'))])
        )
        if cbsp_match := concrete_bytearray_size_pattern.match(constraint):
            new_i = simplify_int(cbsp_match['V1'])
            if self._current_schedule and self.opcode_lookup(cbsp_match['V2'], new_i, self._current_schedule):
                return mlTop()
            return mlEqualsTrue(KApply('_<Int_', [new_i, KEVM.size_bytearray(cbsp_match['V2'])]))

        # { true #Equals isAddr1Op(OP) }
        # { true #Equals isAddr2Op(OP) }
        # { true #Equals notBool (isAddr1Op(OP) orBool isAddr2Op(OP)) }
        addr1_op_pattern = mlEqualsTrue(KApply('isAddr1Op(_)_EVM_Bool_OpCode', [KVariable('OP')]))
        if aop_match := addr1_op_pattern.match(constraint):
            return mlTop() if KEVM.is_addr1_op(aop_match['OP']) else mlBottom()
        addr2_op_pattern = mlEqualsTrue(KApply('isAddr2Op(_)_EVM_Bool_OpCode', [KVariable('OP')]))
        if aop_match := addr2_op_pattern.match(constraint):
            return mlTop() if KEVM.is_addr2_op(aop_match['OP']) else mlBottom()
        not_addr_op_pattern = mlEqualsTrue(
            notBool(
                orBool(
                    [
                        KApply('isAddr1Op(_)_EVM_Bool_OpCode', [KVariable('OP')]),
                        KApply('isAddr2Op(_)_EVM_Bool_OpCode', [KVariable('OP')]),
                    ]
                )
            )
        )
        if aop_match := not_addr_op_pattern.match(constraint):
            return (
                mlTop() if not (KEVM.is_addr1_op(aop_match['OP']) or KEVM.is_addr2_op(aop_match['OP'])) else mlBottom()
            )

        # { true #Equals Ghasaccesslist << SCHED >> }
        # { true #Equals notBool Ghasaccesslist << SCHED >> }
        has_access_list = KApply(
            '_<<_>>_EVM_Bool_ScheduleFlag_Schedule', [KApply('Ghasaccesslist_EVM_ScheduleFlag'), KVariable('SCHED')]
        )
        has_access_list_pattern = mlEqualsTrue(has_access_list)
        if halp_match := has_access_list_pattern.match(constraint):
            if halp_match and type(halp_match['SCHED']) is KApply:
                return mlTop() if KEVM.has_access_list(halp_match['SCHED']) else mlBottom()
        no_has_access_list_pattern = mlEqualsTrue(notBool(has_access_list))
        if nhalp_match := no_has_access_list_pattern.match(constraint):
            if nhalp_match and type(nhalp_match['SCHED']) is KApply:
                return mlTop() if not KEVM.has_access_list(nhalp_match['SCHED']) else mlBottom()

        # { true #Equals #usesMemory(OP) }
        # { true #Equals notBool #usesMemory(OP) }
        uses_memory_pattern = mlEqualsTrue(KApply('#usesMemory(_)_EVM_Bool_OpCode', [KVariable('OP')]))
        if ump_match := uses_memory_pattern.match(constraint):
            return mlTop() if KEVM.uses_memory(ump_match['OP']) else mlBottom()
        not_uses_memory_pattern = mlEqualsTrue(notBool(KApply('#usesMemory(_)_EVM_Bool_OpCode', [KVariable('OP')])))
        if nump_match := not_uses_memory_pattern.match(constraint):
            return mlTop() if not KEVM.uses_memory(nump_match['OP']) else mlBottom()

        return constraint

    def init_state(self, cterm: CTerm) -> None:
        config, *constraints = cterm
        _, subst = split_config_from(config)
        sched_cell = subst['SCHEDULE_CELL']
        program_cell = subst['PROGRAM_CELL']
        self._current_schedule = sched_cell
        self.add_opcode_table(program_cell, sched_cell)

    def simplify(self, cterm: CTerm) -> Optional[CTerm]:
        config, *constraints = cterm
        empty_config, subst = split_config_from(config)

        # <k> #next [ #dasmOpCode(PROGRAM [ PC ], SCHED) ] ~> REST </k>
        byte_lookup_pattern = KApply('_[_]_BYTES-HOOKED_Int_Bytes_Int', [KVariable('PROGRAM'), KVariable('PC')])
        k_cell_pattern = KSequence(
            [
                KEVM.next_op(
                    KApply('#dasmOpCode(_,_)_EVM_OpCode_Int_Schedule', [byte_lookup_pattern, KVariable('SCHED')])
                ),
                KVariable('REST'),
            ]
        )
        if k_cell_match := k_cell_pattern.match(subst['K_CELL']):
            pcount = k_cell_match['PC']
            opcode_info = self.opcode_lookup(k_cell_match['PROGRAM'], pcount, k_cell_match['SCHED'])
            if opcode_info:
                nop, _ = opcode_info
                subst['K_CELL'] = KSequence([KEVM.next_op(nop), k_cell_match['REST']])

        # <k> #exec [ OP ] ~> REST </k> <wordStack> WS </wordStack>
        k_pattern = KSequence([KApply('#exec[_]_EVM_InternalOp_OpCode', [KVariable('OP')]), KVariable('REST')])
        wordstack_items = KEVM.wordstack_items(subst['WORDSTACK_CELL'])
        if len(wordstack_items) > 0 and wordstack_items[-1] == KEVM.wordstack_empty():
            if kp_match := k_pattern.match(subst['K_CELL']):
                op = kp_match['OP']
                rest = kp_match['REST']
                if type(op) is KApply:
                    if op.label.name.endswith('NullStackOp'):
                        subst['K_CELL'] = KSequence([KEVM.gas_op(op, op), op, rest])
                    else:
                        opp_array = [
                            ('UnStackOp', 1, '___EVM_InternalOp_UnStackOp_Int'),
                            ('BinStackOp', 2, '____EVM_InternalOp_BinStackOp_Int_Int'),
                            ('TernStackOp', 3, '____EVM_InternalOp_TernStackOp_Int_Int_Int'),
                            ('QuadStackOp', 4, '____EVM_InternalOp_QuadStackOp_Int_Int_Int_Int'),
                        ]
                        for suffix, n_items, label in opp_array:
                            if op.label.name.endswith(suffix) and len(wordstack_items) >= n_items:
                                new_op = KApply(label, [op] + wordstack_items[0:n_items])
                                subst['WORDSTACK_CELL'] = KEVM.wordstack(wordstack_items[n_items:-1])
                                subst['K_CELL'] = KSequence([KEVM.gas_op(op, new_op), new_op, rest])

        # <pc> PCOUNT </pc>
        subst['PC_CELL'] = self.simplify_int(subst['PC_CELL'])

        # <gas> GAS </gas>
        subst['GAS_CELL'] = self.simplify_int(subst['GAS_CELL'])

        return CTerm(mlAnd([Subst(subst)(empty_config)] + constraints))

    def rewrite_step(self, cterm: CTerm) -> Optional[CTerm]:
        next_cterms: List[Tuple[int, CTerm]] = []
        rules = self.indexed_rules(cterm)
        min_priority = 500
        for priority, lhs, rhs in rules:
            # TODO: needs to be unify_with_constraint instead
            # TODO: or needs to have routine "does not unify" for other rules
            rule_match = lhs.match_with_constraint(cterm)
            if rule_match:
                # TODO: CTerm.match_with_constraint should return a Subst
                _subst, constraint = rule_match
                subst = Subst(_subst)
                new_config = subst(rhs.config)
                new_constraints = [
                    self.simplify_constraint(subst(c)) for c in list(lhs.constraints) + list(rhs.constraints)
                ]
                if not any(map(is_bottom, new_constraints)):
                    next_cterm = self.simplify(CTerm(mlAnd([new_config] + new_constraints)))
                    if next_cterm is not None:
                        next_cterms.append((priority, next_cterm))
                        if priority < min_priority:
                            min_priority = priority
        highest_priority = [ct for p, ct in next_cterms if p == min_priority]
        if len(highest_priority) < len(next_cterms):
            _LOGGER.warning(f'Discarding {len(next_cterms) - len(highest_priority)} lower priority states.')
        _LOGGER.info(f'Number of next states: {len(highest_priority)}')
        if len(highest_priority) == 1:
            return highest_priority[0]
        elif len(highest_priority) > 1:
            for nc in highest_priority:
                next_k = get_cell(nc.config, 'K_CELL')
                _LOGGER.info(f'Next state: {self.pretty_print(mlAnd([next_k] + list(nc.constraints)))}')
        return None

    def get_basic_block_fast(self, init_cterm: CTerm) -> Tuple[int, CTerm]:
        self.init_state(init_cterm)
        depth = 0
        _curr_cterm = init_cterm
        while next_cterm := self.rewrite_step(_curr_cterm):
            depth += 1
            _curr_cterm = next_cterm
        _new_k_cell = get_cell(_curr_cterm.config, 'K_CELL')
        _new_constraints = list(_curr_cterm.constraints)
        _LOGGER.info(
            f'Took {depth} steps with fast rewriter to get state: {self.pretty_print(mlAnd([_new_k_cell] + _new_constraints))}'
        )
        return depth, _curr_cterm

    @staticmethod
    def kompile(
        definition_dir: Path,
        backend: KompileBackend,
        main_file: Path,
        emit_json: bool = True,
        includes: Iterable[str] = (),
        main_module_name: Optional[str] = None,
        syntax_module_name: Optional[str] = None,
        md_selector: Optional[str] = None,
        profile: bool = False,
        debug: bool = False,
        ccopts: Iterable[str] = (),
        llvm_kompile: bool = True,
        optimization: int = 0,
    ) -> 'KEVM':
        command = ['kompile', '--output-definition', str(definition_dir), str(main_file)]
        if debug:
            command += ['--debug']
        command += ['--backend', backend.value]
        command += ['--main-module', main_module_name] if main_module_name else []
        command += ['--syntax-module', syntax_module_name] if syntax_module_name else []
        command += ['--md-selector', md_selector] if md_selector else []
        command += ['--hook-namespaces', ' '.join(KEVM.hook_namespaces())]
        command += add_include_arg(includes)
        if emit_json:
            command += ['--emit-json']
        if backend == KompileBackend.HASKELL:
            command += ['--concrete-rules', ','.join(KEVM.concrete_rules())]
        if backend == KompileBackend.LLVM:
            if ccopts:
                for ccopt in ccopts:
                    command += ['-ccopt', ccopt]
            if 0 < optimization and optimization <= 3:
                command += [f'-O{optimization}']
            if not llvm_kompile:
                command += ['--no-llvm-kompile']
        try:
            run_process(command, logger=_LOGGER, profile=profile)
        except CalledProcessError as err:
            sys.stderr.write(f'\nkompile stdout:\n{err.stdout}\n')
            sys.stderr.write(f'\nkompile stderr:\n{err.stderr}\n')
            sys.stderr.write(f'\nkompile returncode:\n{err.returncode}\n')
            sys.stderr.flush()
            raise
        return KEVM(definition_dir, main_file=main_file)

    @staticmethod
    def _patch_symbol_table(symbol_table: Dict[str, Any]) -> None:
        # fmt: off
        symbol_table['#Bottom']                                       = lambda: '#Bottom'
        symbol_table['_orBool_']                                      = paren(symbol_table['_orBool_'])
        symbol_table['_andBool_']                                     = paren(symbol_table['_andBool_'])
        symbol_table['_impliesBool_']                                 = paren(symbol_table['_impliesBool_'])
        symbol_table['notBool_']                                      = paren(symbol_table['notBool_'])
        symbol_table['_/Int_']                                        = paren(symbol_table['_/Int_'])
        symbol_table['_*Int_']                                        = paren(symbol_table['_*Int_'])
        symbol_table['_-Int_']                                        = paren(symbol_table['_-Int_'])
        symbol_table['_+Int_']                                        = paren(symbol_table['_+Int_'])
        symbol_table['_&Int_']                                        = paren(symbol_table['_&Int_'])
        symbol_table['_|Int_']                                        = paren(symbol_table['_|Int_'])
        symbol_table['_modInt_']                                      = paren(symbol_table['_modInt_'])
        symbol_table['#Or']                                           = paren(symbol_table['#Or'])
        symbol_table['#And']                                          = paren(symbol_table['#And'])
        symbol_table['#Implies']                                      = paren(symbol_table['#Implies'])
        symbol_table['_Set_']                                         = paren(symbol_table['_Set_'])
        symbol_table['_|->_']                                         = paren(symbol_table['_|->_'])
        symbol_table['_Map_']                                         = paren(lambda m1, m2: m1 + '\n' + m2)
        symbol_table['_AccountCellMap_']                              = paren(lambda a1, a2: a1 + '\n' + a2)
        symbol_table['.AccountCellMap']                               = lambda: '.Bag'
        symbol_table['AccountCellMapItem']                            = lambda k, v: v
        symbol_table['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray'] = paren(lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]')
        symbol_table['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int'] = paren(lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray')
        symbol_table['_:__EVM-TYPES_WordStack_Int_WordStack']         = paren(symbol_table['_:__EVM-TYPES_WordStack_Int_WordStack'])
        symbol_table['_<Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')
        symbol_table['_>Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')
        symbol_table['_<=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')
        symbol_table['_>=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')
        symbol_table['_==Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')
        symbol_table['_s<Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')
        symbol_table['_[_]_EVM-TYPES_Int_WordStack_Int']              = paren(symbol_table['_[_]_EVM-TYPES_Int_WordStack_Int'])
        symbol_table['_++__EVM-TYPES_ByteArray_ByteArray_ByteArray']  = paren(symbol_table['_++__EVM-TYPES_ByteArray_ByteArray_ByteArray'])
        if 'typedArgs' in symbol_table:
            symbol_table['typedArgs'] = paren(symbol_table['typedArgs'])
        # fmt: on

    class Sorts:
        KEVM_CELL: Final = KSort('KevmCell')

    @staticmethod
    def hook_namespaces() -> List[str]:
        return ['JSON', 'KRYPTO', 'BLOCKCHAIN']

    @staticmethod
    def concrete_rules() -> List[str]:
        return [
            'EVM.allBut64th.pos',
            'EVM.Caddraccess',
            'EVM.Cbalance.new',
            'EVM.Cbalance.old',
            'EVM.Cextcodecopy.new',
            'EVM.Cextcodecopy.old',
            'EVM.Cextcodehash.new',
            'EVM.Cextcodehash.old',
            'EVM.Cextcodesize.new',
            'EVM.Cextcodesize.old',
            'EVM.Cextra.new',
            'EVM.Cextra.old',
            'EVM.Cgascap',
            'EVM.Cmem',
            'EVM.Cmodexp.new',
            'EVM.Cmodexp.old',
            'EVM.Csload.new',
            'EVM.Csstore.new',
            'EVM.Csstore.old',
            'EVM.Cstorageaccess',
            'EVM.ecrec',
            'EVM.#memoryUsageUpdate.some',
            'EVM.Rsstore.new',
            'EVM.Rsstore.old',
            'EVM-TYPES.#asByteStack',
            'EVM-TYPES.#asByteStackAux.recursive',
            'EVM-TYPES.#asWord.recursive',
            'EVM-TYPES.ByteArray.range',
            'EVM-TYPES.bytesRange',
            'EVM-TYPES.mapWriteBytes.recursive',
            'EVM-TYPES.#padRightToWidth',
            'EVM-TYPES.#padToWidth',
            'EVM-TYPES.padToWidthNonEmpty',
            'EVM-TYPES.powmod.nonzero',
            'EVM-TYPES.powmod.zero',
            'EVM-TYPES.#range',
            'EVM-TYPES.signextend.invalid',
            'EVM-TYPES.signextend.negative',
            'EVM-TYPES.signextend.positive',
            'EVM-TYPES.upDivInt',
            'SERIALIZATION.keccak',
            'SERIALIZATION.#newAddr',
            'SERIALIZATION.#newAddrCreate2',
        ]

    @staticmethod
    def add_invariant(cterm: CTerm) -> CTerm:
        config, *constraints = cterm

        word_stack = get_cell(config, 'WORDSTACK_CELL')
        if type(word_stack) is not KVariable:
            word_stack_items = flatten_label('_:__EVM-TYPES_WordStack_Int_WordStack', word_stack)
            for i in word_stack_items[:-1]:
                constraints.append(mlEqualsTrue(KEVM.range_uint(256, i)))

        gas_cell = get_cell(config, 'GAS_CELL')
        if not (type(gas_cell) is KApply and gas_cell.label.name == 'infGas'):
            constraints.append(mlEqualsTrue(KEVM.range_uint(256, gas_cell)))
        constraints.append(mlEqualsTrue(KEVM.range_address(get_cell(config, 'ID_CELL'))))
        constraints.append(mlEqualsTrue(KEVM.range_address(get_cell(config, 'CALLER_CELL'))))
        constraints.append(mlEqualsTrue(KEVM.range_address(get_cell(config, 'ORIGIN_CELL'))))
        constraints.append(mlEqualsTrue(ltInt(KEVM.size_bytearray(get_cell(config, 'CALLDATA_CELL')), KEVM.pow256())))

        return CTerm(mlAnd([config] + list(unique(constraints))))

    @staticmethod
    def extract_branches(cterm: CTerm) -> Iterable[KInner]:
        config, *constraints = cterm
        k_cell = get_cell(config, 'K_CELL')
        jumpi_pattern = KEVM.jumpi_applied(KVariable('###PCOUNT'), KVariable('###COND'))
        pc_next_pattern = KApply('#pc[_]_EVM_InternalOp_OpCode', [KEVM.jumpi()])
        branch_pattern = KSequence([jumpi_pattern, pc_next_pattern, KEVM.execute(), KVariable('###CONTINUATION')])
        if subst := branch_pattern.match(k_cell):
            cond = subst['###COND']
            if cond_subst := KEVM.bool_2_word(KVariable('###BOOL_2_WORD')).match(cond):
                cond = cond_subst['###BOOL_2_WORD']
            else:
                cond = KApply('_==Int_', [cond, intToken(0)])
            return [mlEqualsTrue(cond), mlEqualsTrue(KApply('notBool', [cond]))]
        return []

    @staticmethod
    def is_terminal(cterm: CTerm) -> bool:
        config, *_ = cterm
        k_cell = get_cell(config, 'K_CELL')
        # <k> #halt </k>
        if k_cell == KEVM.halt():
            return True
        elif type(k_cell) is KSequence:
            # <k> #halt ~> _ </k>
            if k_cell and k_cell[0] == KEVM.halt():
                # #Not (<k> #halt ~> #execute ~> _ </k>)
                if len(k_cell) > 1 and k_cell[1] != KEVM.execute():
                    return True
        return False

    @staticmethod
    def halt() -> KApply:
        return KApply('#halt_EVM_KItem')

    @staticmethod
    def execute() -> KApply:
        return KApply('#execute_EVM_KItem')

    @staticmethod
    def next_op(op: KInner) -> KApply:
        return KApply('#next[_]_EVM_InternalOp_OpCode', [op])

    @staticmethod
    def gas_op(op: KInner, op_applied: KInner) -> KApply:
        return KApply('#gas[_,_]_EVM_InternalOp_OpCode_OpCode', [op, op_applied])

    @staticmethod
    def jumpi() -> KApply:
        return KApply('JUMPI_EVM_BinStackOp')

    @staticmethod
    def jump() -> KApply:
        return KApply('JUMP_EVM_UnStackOp')

    @staticmethod
    def jumpi_applied(pc: KInner, cond: KInner) -> KApply:
        return KApply('____EVM_InternalOp_BinStackOp_Int_Int', [KEVM.jumpi(), pc, cond])

    @staticmethod
    def jump_applied(pc: KInner) -> KApply:
        return KApply('___EVM_InternalOp_UnStackOp_Int', [KEVM.jump(), pc])

    @staticmethod
    def pow256() -> KApply:
        return KApply('pow256_WORD_Int', [])

    @staticmethod
    def range_uint(width: int, i: KInner) -> KApply:
        return KApply('#rangeUInt(_,_)_WORD_Bool_Int_Int', [intToken(width), i])

    @staticmethod
    def range_sint(width: int, i: KInner) -> KApply:
        return KApply('#rangeSInt(_,_)_WORD_Bool_Int_Int', [intToken(width), i])

    @staticmethod
    def range_address(i: KInner) -> KApply:
        return KApply('#rangeAddress(_)_WORD_Bool_Int', [i])

    @staticmethod
    def range_bool(i: KInner) -> KApply:
        return KApply('#rangeBool(_)_WORD_Bool_Int', [i])

    @staticmethod
    def range_bytes(width: KInner, ba: KInner) -> KApply:
        return KApply('#rangeBytes(_,_)_WORD_Bool_Int_Int', [width, ba])

    @staticmethod
    def bool_2_word(cond: KInner) -> KApply:
        return KApply('bool2Word(_)_EVM-TYPES_Int_Bool', [cond])

    @staticmethod
    def size_bytearray(ba: KInner) -> KApply:
        return KApply('#sizeByteArray(_)_EVM-TYPES_Int_ByteArray', [ba])

    @staticmethod
    def inf_gas(g: KInner) -> KApply:
        return KApply('infGas', [g])

    @staticmethod
    def compute_valid_jumpdests(p: KInner) -> KApply:
        return KApply('#computeValidJumpDests(_)_EVM_Set_ByteArray', [p])

    @staticmethod
    def bin_runtime(c: KInner) -> KApply:
        return KApply('binRuntime', [c])

    @staticmethod
    def hashed_location(compiler: str, base: KInner, offset: KInner, member_offset: int = 0) -> KApply:
        location = KApply(
            '#hashedLocation(_,_,_)_HASHED-LOCATIONS_Int_String_Int_IntList', [stringToken(compiler), base, offset]
        )
        if member_offset > 0:
            location = KApply('_+Int_', [location, intToken(member_offset)])
        return location

    @staticmethod
    def loc(accessor: KInner) -> KApply:
        return KApply('contract_access_loc', [accessor])

    @staticmethod
    def lookup(map: KInner, key: KInner) -> KApply:
        return KApply('#lookup(_,_)_EVM-TYPES_Int_Map_Int', [map, key])

    @staticmethod
    def abi_calldata(name: str, args: List[KInner]) -> KApply:
        return KApply(
            '#abiCallData(_,_)_EVM-ABI_ByteArray_String_TypedArgs', [stringToken(name), KEVM.typed_args(args)]
        )

    @staticmethod
    def abi_selector(name: str) -> KApply:
        return KApply('abi_selector', [stringToken(name)])

    @staticmethod
    def abi_address(a: KInner) -> KApply:
        return KApply('#address(_)_EVM-ABI_TypedArg_Int', [a])

    @staticmethod
    def abi_bool(b: KInner) -> KApply:
        return KApply('#bool(_)_EVM-ABI_TypedArg_Int', [b])

    @staticmethod
    def abi_type(type: str, value: KInner) -> KApply:
        return KApply('abi_type_' + type, [value])

    @staticmethod
    def empty_typedargs() -> KApply:
        return KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')

    @staticmethod
    def bytes_append(b1: KInner, b2: KInner) -> KApply:
        return KApply('_++__EVM-TYPES_ByteArray_ByteArray_ByteArray', [b1, b2])

    @staticmethod
    def account_cell(
        id: KInner, balance: KInner, code: KInner, storage: KInner, orig_storage: KInner, nonce: KInner
    ) -> KApply:
        return KApply(
            '<account>',
            [
                KApply('<acctID>', [id]),
                KApply('<balance>', [balance]),
                KApply('<code>', [code]),
                KApply('<storage>', [storage]),
                KApply('<origStorage>', [orig_storage]),
                KApply('<nonce>', [nonce]),
            ],
        )

    @staticmethod
    def wordstack_empty() -> KInner:
        return KApply('.WordStack_EVM-TYPES_WordStack')

    @staticmethod
    def wordstack(items: Iterable[KInner]) -> KInner:
        return build_cons(KEVM.wordstack_empty(), '_:__EVM-TYPES_WordStack_Int_WordStack', items)

    @staticmethod
    def wordstack_items(ws: KInner) -> List[KInner]:
        return flatten_label('_:__EVM-TYPES_WordStack_Int_WordStack', ws)

    @staticmethod
    def wordstack_len(constrained_term: KInner) -> int:
        return len(KEVM.wordstack_items(get_cell(constrained_term, 'WORDSTACK_CELL')))

    @staticmethod
    def parse_bytestack(s: KInner) -> KApply:
        return KApply('#parseByteStack(_)_SERIALIZATION_ByteArray_String', [s])

    @staticmethod
    def bytearray_empty() -> KApply:
        return KApply('.ByteArray_EVM-TYPES_ByteArray')

    @staticmethod
    def intlist(ints: List[KInner]) -> KApply:
        res = KApply('.List{"___HASHED-LOCATIONS_IntList_Int_IntList"}_IntList')
        for i in reversed(ints):
            res = KApply('___HASHED-LOCATIONS_IntList_Int_IntList', [i, res])
        return res

    @staticmethod
    def typed_args(args: List[KInner]) -> KApply:
        res = KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')
        for i in reversed(args):
            res = KApply('_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs', [i, res])
        return res

    @staticmethod
    def accounts(accts: List[KInner]) -> KInner:
        return build_assoc(KApply('.AccountCellMap'), KLabel('_AccountCellMap_'), accts)

    @staticmethod
    def stack_needed(op: KInner) -> Optional[int]:
        if type(op) is KApply:
            if op.label.name == 'PUSH(_)_EVM_PushOp_Int':
                return 0
            if op.label.name.endswith('NullStackOp'):
                return 0
            if op.label.name.endswith('UnStackOp'):
                return 1
            if op.label.name.endswith('BinStackOp'):
                return 2
            if op.label.name.endswith('TernStackOp'):
                return 3
            if op.label.name.endswith('QuadStackOp'):
                return 4
        return None

    @staticmethod
    def width_op(op: KInner) -> int:
        if type(op) is KApply and op.label.name == 'PUSH(_)_EVM_PushOp_Int':
            width = op.args[0]
            assert type(width) is KToken
            return 1 + int(width.token)
        return 1

    @staticmethod
    def is_addr1_op(op: KInner) -> bool:
        return type(op) is KApply and op.label.name in {
            'BALANCE_EVM_UnStackOp',
            'SELFDESTRUCT_EVM_UnStackOp',
            'EXTCODEHASH_EVM_UnStackOp',
            'EXTCODESIZE_EVM_UnStackOp',
            'EXTCODECOPY_EVM_QuadStackOp',
        }

    @staticmethod
    def is_addr2_op(op: KInner) -> bool:
        return type(op) is KApply and op.label.name in {
            'CALLCODE_EVM_CallOp',
            'CALL_EVM_CallOp',
            'DELEGATECALL_EVM_CallSixOp',
            'STATICCALL_EVM_CallSixOp',
        }

    @staticmethod
    def has_access_list(schedule: KInner) -> bool:
        return type(schedule) is KApply and schedule.label.name in {
            'LONDON_EVM',
            'BERLIN_EVM',
        }

    @staticmethod
    def uses_memory(op: KInner) -> bool:
        return type(op) is KApply and op.label.name in {
            'MLOAD_EVM_UnStackOp',
            'MSTORE_EVM_BinStackOp',
            'MSTORE8_EVM_BinStackOp',
            'SHA3_EVM_BinStackOp',
            'CODECOPY_EVM_TernStackOp',
            'EXTCODECOPY_EVM_QuadStackOp',
            'CALLDATACOPY_EVM_TernStackOp',
            'RETURNDATACOPY_EVM_TernStackOp',
            'CREATE_EVM_TernStackOp',
            'CREATE2_EVM_QuadStackOp',
            'RETURN_EVM_BinStackOp',
            'REVERT_EVM_BinStackOp',
            'LOG(_)_EVM_LogOp_Int',
            'CALLCODE_EVM_CallOp',
            'CALL_EVM_CallOp',
            'DELEGATECALL_EVM_CallSixOp',
            'STATICCALL_EVM_CallSixOp',
        }


class Foundry(KEVM):
    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        profile: bool = False,
    ) -> None:
        KEVM.__init__(self, definition_dir, main_file=main_file, use_directory=use_directory, profile=profile)
        Foundry._patch_symbol_table(self.symbol_table)

    class Sorts:
        FOUNDRY_CELL: Final = KSort('FoundryCell')

    @staticmethod
    def _patch_symbol_table(symbol_table: Dict[str, Any]) -> None:
        KEVM._patch_symbol_table(symbol_table)

    @staticmethod
    def success(s: KInner, dst: KInner) -> KApply:
        return KApply('foundry_success ', [s, dst])

    @staticmethod
    def fail(s: KInner, dst: KInner) -> KApply:
        return notBool(Foundry.success(s, dst))

    # address(uint160(uint256(keccak256("foundry default caller"))))

    @staticmethod
    def address_CALLER() -> KToken:  # noqa: N802
        return intToken(0x1804C8AB1F12E6BBF3894D4083F33E07309D1F38)

    @staticmethod
    def account_CALLER() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_CALLER(), intToken(0), KEVM.bytearray_empty(), KApply('.Map'), KApply('.Map'), intToken(0)
        )

    @staticmethod
    def address_TEST_CONTRACT() -> KToken:  # noqa: N802
        return intToken(0xB4C79DAB8F259C7AEE6E5B2AA729821864227E84)

    @staticmethod
    def account_TEST_CONTRACT_ADDRESS() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_TEST_CONTRACT(),
            intToken(0),
            KVariable('TEST_CODE'),
            KApply('.Map'),
            KApply('.Map'),
            intToken(0),
        )

    @staticmethod
    def address_CHEATCODE() -> KToken:  # noqa: N802
        return intToken(0x7109709ECFA91A80626FF3989D68F67F5B1DD12D)

    # Same address as the one used in DappTools's HEVM
    # address(bytes20(uint160(uint256(keccak256('hevm cheat code')))))
    @staticmethod
    def account_CHEATCODE_ADDRESS(store_var: KInner) -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_CHEATCODE(),  # Hardcoded for now
            intToken(0),
            KToken('b"\\x00"', 'Bytes'),
            store_var,
            KApply('.Map'),
            intToken(0),
        )

    @staticmethod
    def address_HARDHAT_CONSOLE() -> KToken:  # noqa: N802
        return intToken(0x000000000000000000636F6E736F6C652E6C6F67)

    # Hardhat console address (0x000000000000000000636F6e736F6c652e6c6f67)
    # https://github.com/nomiclabs/hardhat/blob/master/packages/hardhat-core/console.sol
    @staticmethod
    def account_HARDHAT_CONSOLE_ADDRESS() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_HARDHAT_CONSOLE(),
            intToken(0),
            KEVM.bytearray_empty(),
            KApply('.Map'),
            KApply('.Map'),
            intToken(0),
        )
