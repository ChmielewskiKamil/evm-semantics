import logging
import sys
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Callable, Dict, Final, Iterable, List, Optional, Tuple

from pyk.cli_utils import run_process
from pyk.cterm import CTerm
from pyk.kast import KApply, KInner, KLabel, KRule, KSequence, KSort, KToken, KVariable, Subst, build_assoc
from pyk.kastManip import bool_to_ml_pred, extract_lhs, extract_rhs, flatten_label, get_cell
from pyk.ktool import KProve, KRun
from pyk.ktool.kompile import KompileBackend
from pyk.ktool.kprint import paren
from pyk.prelude.kbool import notBool
from pyk.prelude.kint import intToken, ltInt
from pyk.prelude.ml import mlAnd, mlEqualsTrue
from pyk.prelude.string import stringToken
from pyk.utils import unique

from .utils import KDefinition__semantic_rules, add_include_arg

_LOGGER: Final = logging.getLogger(__name__)


# KEVM class


class KEVM(KProve, KRun):
    semantic_rules: List[KRule]
    _rule_index: Optional[Callable[[CTerm], List[KRule]]]
    _opcode_lookup: Dict[KInner, Dict[KInner, Tuple[KInner, int]]]

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
        self.semantic_rules = KDefinition__semantic_rules(self.definition)
        self._rule_index = None
        self._opcode_lookup = {}

    @property
    def rule_index(self) -> Callable[[CTerm], List[KRule]]:
        if not self._rule_index:

            def __rule_index(_cterm: CTerm) -> List[KRule]:
                return self.semantic_rules

            self._rule_index = __rule_index
        return self._rule_index

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

    def opcode_lookup(self, program: KInner, pcount: KInner, schedule: KInner) -> Optional[Tuple[KInner, int]]:
        if program not in self._opcode_lookup:
            _LOGGER.info(f'Computing bytecode disassembly: {self.pretty_print(program)}')
            lookup_evm_pgm = KApply('dasm_program___FOUNDRY_EthereumSimulation_ByteArray_Schedule', [program, schedule])
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
            if type(k_cell) is KSequence and len(k_cell.items) > 0:
                k_cell = k_cell.items[0]
            if type(k_cell) is KApply and k_cell.label.name == 'dasm_result__FOUNDRY_EthereumSimulation_Map':
                self._opcode_lookup[program] = KEVM.opcode_map_to_dict(k_cell.args[0])
            _LOGGER.info(f'result: {self._opcode_lookup[program]}')

        if program in self._opcode_lookup and pcount in self._opcode_lookup[program]:
            return self._opcode_lookup[program][pcount]

        return None

    def rewrite_step(self, cterm: CTerm) -> Optional[CTerm]:
        next_cterms: List[CTerm] = []
        rules = self.rule_index(cterm)
        _LOGGER.info(f'Found {len(rules)} rules in index.')
        for r in rules:
            rule_lhs = CTerm(mlAnd([extract_lhs(r.body), bool_to_ml_pred(r.requires)]))
            # TODO: needs to be unify_with_constraint instead
            rule_k_cell = get_cell(rule_lhs.config, 'K_CELL')
            term_k_cell = get_cell(cterm.config, 'K_CELL')
            k_cell_match = rule_k_cell.match(term_k_cell)
            _LOGGER.info(
                'K Cell Match:\n'
                f'Rule K Cell: {self.pretty_print(rule_k_cell)}\n'
                f'Term K Cell: {self.pretty_print(term_k_cell)}\n'
                f'Match: {k_cell_match}\n'
            )
            rule_match = rule_lhs.match_with_constraint(cterm)
            if rule_match:
                # TODO: CTerm.match_with_constraint should return a Subst
                _subst, constraint = rule_match
                subst = Subst(_subst)
                next_cterm = CTerm(subst(mlAnd([extract_rhs(r.body), bool_to_ml_pred(r.ensures)])))
                next_cterm = next_cterm.add_constraint(constraint)
                next_cterms.append(next_cterm)
        if len(next_cterms) == 1:
            return next_cterms[0]
        return None

    def get_basic_block_fast(self, init_cterm: CTerm) -> Tuple[int, CTerm]:
        depth = 0
        _curr_cterm = init_cterm
        while next_cterm := self.rewrite_step(_curr_cterm):
            depth += 1
            _curr_cterm = next_cterm
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
        symbol_table['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int'] = lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray'
        symbol_table['_:__EVM-TYPES_WordStack_Int_WordStack']         = paren(symbol_table['_:__EVM-TYPES_WordStack_Int_WordStack'])
        symbol_table['_<Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')
        symbol_table['_>Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')
        symbol_table['_<=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')
        symbol_table['_>=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')
        symbol_table['_==Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')
        symbol_table['_s<Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')
        symbol_table['_[_]_EVM-TYPES_Int_WordStack_Int']              = paren(symbol_table['_[_]_EVM-TYPES_Int_WordStack_Int'])
        symbol_table['_++__EVM-TYPES_ByteArray_ByteArray_ByteArray']  = paren(symbol_table['_++__EVM-TYPES_ByteArray_ByteArray_ByteArray'])
        symbol_table['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int'] = paren(symbol_table['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int'])
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
    def wordstack_len(constrained_term: KInner) -> int:
        return len(flatten_label('_:__EVM-TYPES_WordStack_Int_WordStack', get_cell(constrained_term, 'WORDSTACK_CELL')))

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
