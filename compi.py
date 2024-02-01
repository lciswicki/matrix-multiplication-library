#!/usr/bin/env python3

#
# Usage: `python3 (path)/jftt2018-compiler.py` or simply `(path)/jftt2018-compiler.py`
# Requirements: `pip3 install sly`
#

import sly
import sys

import collections
import enum
from pprint import pprint
import random


def frozen_hash(obj):
    """ Compute a hash over a set or dict by converting it to frozenset/"frozendict" """
    if isinstance(obj, set):
        tmp = frozenset(obj)
        return hash(tmp)
    elif isinstance(obj, dict):
        tmp = tuple(sorted(obj.iteritems()))
        return hash(tmp)
    else:
        return hash(obj)


def reversed_enumerate(lst):
    rev = reversed(lst)
    rng = range(len(lst)-1, -1, -1)
    return zip(rng, rev)


class Bunch:
    def __init__(self, **kwargs):
        for k, v in kwargs.items():
            setattr(self, k, v)


class CompilerError(Exception):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)


class Variable:
    instances = {}
    @classmethod
    def get(cls, name, isloopcounter=False):
        try:
            return cls.instances[name]
        except KeyError:
            instance = cls(name, isloopcounter)
            cls.instances[name] = instance
            return instance

    def __init__(self, name, isloopcounter=False):
        self.name = name
        self.isarray = False
        self.isloopcounter = isloopcounter
        self.irdefcount = 0
        self.memidx = None

    def nextirvar(self):
        self.irdefcount += 1
        label = '{}${}'.format(self.name, self.irdefcount)

        return label

    def emit_load(self, irbuilder):
        # Default implementation for scalars
        irvar = self.nextirvar()
        instr = irbuilder.add_var(irvar, InstrClass.SLOAD, self)
        return instr

    def emit_store(self, irbuilder, value):
        # Default implementation for scalars
        irbuilder.add_instr(InstrClass.SSTORE, self, value)

    def __repr__(self):
        return '${}'.format(self.name)
    
    def __hash__(self):
        return hash((self.name, self.isarray, self.isloopcounter))

class ArrayVariable(Variable):
    @classmethod
    def get(cls, name, start: int, stop: int):
        try:
            instance = cls.instances[name]
            assert isinstance(instance, cls)
            return instance
        except KeyError:
            instance = cls(name, start, stop)
            cls.instances[name] = instance
            return instance

    def __init__(self, name, start: int, stop: int):
        super().__init__(name, False)
        self.isarray = True
        self.start = start
        self.stop = stop

    def emit_load(self, irbuilder, index):
        # Specialized implementation for arrays
        irvar = self.nextirvar()
        lea_irvar = irbuilder.tmpvar.nextirvar()
        lea_instr = irbuilder.add_var(lea_irvar, InstrClass.LEA, self, index)
        instr = irbuilder.add_var(irvar, InstrClass.SLOAD, lea_instr)
        return instr

    def emit_store(self, irbuilder, index, value):
        # Specialized implementation for arrays
        lea_irvar = irbuilder.tmpvar.nextirvar()
        lea_instr = irbuilder.add_var(lea_irvar, InstrClass.LEA, self, index)
        irbuilder.add_instr(InstrClass.SSTORE, lea_instr, value)

    @property
    def length(self):
        return self.stop - self.start + 1


class InstrClass(enum.Enum):
    # HW-like instruction classes
    GET = (enum.auto(), True, 100, True, True, (0,), (), False)
    PUT = (enum.auto(), True, 100, False, True, (), (0,), False)
    LOAD = (enum.auto(), True, 50, True, False, (0,), (), False)
    STORE = (enum.auto(), True, 50, False, True, (), (0,), False)
    COPY = (enum.auto(), True, 5, True, False, (0,), (1,), False)
    ADD = (enum.auto(), True, 5, True, False, (0,), (0, 1), False)
    SUB = (enum.auto(), True, 5, True, False, (0,), (0, 1), False)
    HALF = (enum.auto(), True, 1, True, False, (0,), (0,), False)
    INC = (enum.auto(), True, 1, True, False, (0,), (0,), False)
    DEC = (enum.auto(), True, 1, True, False, (0,), (0,), False)
    JUMP = (enum.auto(), True, 1, False, True, (), (), True)
    JZERO = (enum.auto(), True, 1, False, True, (), (0,), False)
    JODD = (enum.auto(), True, 1, False, True, (), (0,), False)
    HALT = (enum.auto(), True, 0, False, True, (), (), True)

    # IR-Level pseudoinstructions
    SLOAD = (enum.auto(), False, 0, True, False, (0,), (1,), False)
    SSTORE = (enum.auto(), False, 0, False, True, (0,), (0, 1,), False)  # < TODO: think of a better way to address "def" in memory/spillslot
    CONST = (enum.auto(), False, 0, True, False, (0,), (), False)
    LEA = (enum.auto(), False, 0, True, False, (0,), (1, 2,), False)

    MUL = (enum.auto(), False, 0, True, False, (0,), (0, 1, 2), False)
    # DIV and REM are distinguished at IR level, but during ISel, only DIV instructions are generated
    DIV = (enum.auto(), False, 0, True, False, (0, 3), (0, 1, 2, 3, 4), False)
    REM = (enum.auto(), False, 0, True, False, (), (), False)

    # NO-OP reg definition (reg defined to undef) - to constraint life-ranges for dummy uses
    NOPDEF = (enum.auto(), False, 0, False, False, (0,), (), False)
    # NO-OP reg use (use without effects) - to ensure some VirtRegs are not removed by DCE
    NOPUSE = (enum.auto(), False, 0, False, True, (), (0,), False)

    PHI = (enum.auto(), False, 0, True, False, (), (), False)

    SJZERO = (enum.auto(), False, 0, False, True, (), (0,), True)
    SJODD = (enum.auto(), False, 0, False, True, (), (0,), True)

    def __init__(self, _, machine, cost, irval, protected, mir_def, mir_use, isterm):
        self.ismachine = machine
        self.cost = cost
        self.isirval = irval
        self.isprotected = protected
        self.mir_def = mir_def
        self.mir_use = mir_use
        self.isterm = isterm
    
    def __repr__(self):
        return self.name


class PhysReg(enum.Enum):
    A = 0
    B = 1
    C = 2
    D = 3
    E = 4
    F = 5
    G = 6
    H = 7

    def __repr__(self):
        return '!{}'.format(self.name)
    
    def __lt__(self, other):
        return self.value < other.value


class VirtReg:
    # Static register map
    vregmap = {}

    def __init__(self, name):
        self.name = name
        self.vregmap[name] = self

    @classmethod
    def get(cls, name):
        try:
            return cls.vregmap[name]
        except KeyError:
            vreg = VirtReg(name)
            cls.vregmap[name] = vreg
            return vreg

    def __repr__(self):
        return '@{}'.format(self.name)
    
    def __hash__(self):
        return hash(self.name)


class IRInstr:
    def __init__(self, cls, operands):
        self.cls = cls
        self.operands = operands
    
    def replace(self, cls, operands):
        """
        Effectively replace one instruction with another one.
        Works best for IRValues, as it preserves their names and uses.
        """
        self.cls = cls
        self.operands = operands

    def __str__(self):
        return '{} {}'.format(self.cls.name, self.operands)


class IRValue(IRInstr):
    def __init__(self, cls, name, operands):
        super().__init__(cls, operands)
        self.name = name

    def __str__(self):
        return '%{} = {} {}'.format(self.name, self.cls.name, self.operands)

    def __repr__(self):
        return '%{}'.format(self.name)


class MIRInstr:
    def __init__(self, cls, operands):
        self.cls = cls
        self.operands = operands

    def __str__(self):
        return '{} {}'.format(self.cls.name, self.operands)
    
    def __repr__(self):
        return f"'{self}'"


class IRBuilder:
    def __init__(self, context):
        self.currentbb = None
        self.currentbbname = None
        self.context = context
        self.tmpvar = Variable.get('T')  # An artificial variable for temporary values

    def beginbb(self, bbname='init'):
        self.currentbb = []
        self.currentbbname = bbname
        self.context.bbs[bbname] = self.currentbb

    def switchbb(self, bbname):
        self.currentbb = self.context.bbs[bbname]
        self.currentbbname = bbname

    def add_var(self, irvar, cls, *operands):
        instr = IRValue(cls, irvar, operands)
        self.currentbb.append(instr)
        return instr

    def add_instr(self, cls, *operands):
        instr = IRInstr(cls, operands)
        self.currentbb.append(instr)


class Legalizer:
    def __init__(self, compilercontext):
        self.compilercontext = compilercontext

    def _instr_replacer(self, mbb, instrcls, handler):
        mbb_new = []

        def emit_mir(cls, *operands):
            mbb_new.append(MIRInstr(cls, operands))

        for instr in mbb:
            if instr.cls is instrcls:
                handler(instr, emit_mir)
            else:  # Rewrite all the other instructions
                mbb_new.append(instr)

        return mbb_new
    
    def legalize_noops(self, mbb):
        def replace_noop(instr, emit_mir):
            pass
        
        tmp = self._instr_replacer(mbb, InstrClass.NOPDEF, replace_noop)
        tmp = self._instr_replacer(tmp, InstrClass.NOPUSE, replace_noop)
        return tmp
    
    def legalize_sjumps(self, mbb):
        def replace_sjodd(instr, emit_mir):
            reg = instr.operands[0]
            dst = instr.operands[1]
            fth = instr.operands[2]

            emit_mir(InstrClass.JODD, reg, dst)
            emit_mir(InstrClass.JUMP, fth)
            
        def replace_sjzero(instr, emit_mir):
            reg = instr.operands[0]
            dst = instr.operands[1]
            fth = instr.operands[2]

            emit_mir(InstrClass.JZERO, reg, dst)
            emit_mir(InstrClass.JUMP, fth)

        tmp = self._instr_replacer(mbb, InstrClass.SJODD, replace_sjodd)
        tmp = self._instr_replacer(tmp, InstrClass.SJZERO, replace_sjzero)
        return tmp

    @classmethod
    def estimate_const_cost(self, val):
        rep = bin(val)[2:]
        # Generate the longest prefix s.t. INC-generated prefix is better
        # than SHIFT-INC one
        i = 0
        for i in range(1, len(rep)):
            pref = rep[:i]
            cost_inc = int(pref, 2) * InstrClass.INC.cost
            cost_add = pref.count('1') * InstrClass.INC.cost \
                + (i-1) * InstrClass.ADD.cost
            if cost_add < cost_inc:
                pref = rep[:i-1]
                break
        else:
            pref = rep

        pref_val = int(pref, 2)
        total_cost = InstrClass.SUB.cost
        for _ in range(pref_val):
            total_cost += InstrClass.INC.cost

        for i in range(len(pref), len(rep)):
            total_cost += InstrClass.ADD.cost
            if rep[i] == '1':
                total_cost += InstrClass.INC.cost

        return total_cost

    def legalize_const(self, mbb):
        def replace_const(instr, emit_mir):
            dst = instr.operands[0]
            val = instr.operands[1]

            if isinstance(val, Variable):
                if val.memidx is not None:
                    val = val.memidx
                else:
                    emit_mir(InstrClass.CONST, dst, val)
                    return

            emit_mir(InstrClass.SUB, dst, dst)

            if val > 0:
                rep = bin(val)[2:]
                # Generate the longest prefix s.t. INC-generated prefix is better
                # than SHIFT-INC one
                i = 0
                for i in range(1, len(rep)):
                    pref = rep[:i]
                    cost_inc = int(pref, 2) * InstrClass.INC.cost
                    cost_add = pref.count('1') * InstrClass.INC.cost \
                        + (i-1) * InstrClass.ADD.cost
                    if cost_add < cost_inc:
                        pref = rep[:i-1]
                        break
                else:
                    pref = rep

                pref_val = int(pref, 2)
                for _ in range(pref_val):
                    emit_mir(InstrClass.INC, dst)

                for i in range(len(pref), len(rep)):
                    emit_mir(InstrClass.ADD, dst, dst)
                    if rep[i] == '1':
                        emit_mir(InstrClass.INC, dst)

        return self._instr_replacer(mbb, InstrClass.CONST, replace_const)

    def legalize_lea(self, mbb):
        def replace_lea(instr, emit_mir):
            dst = instr.operands[0]
            arr = instr.operands[1]
            ofs = instr.operands[2]
            arr_start = arr.memidx - arr.start
            if isinstance(ofs, int):
                emit_mir(InstrClass.CONST, dst, arr_start + ofs)
            else:
                emit_mir(InstrClass.COPY, dst, ofs)
                if arr_start < 0:
                    emit_mir(InstrClass.CONST, PhysReg.A, -arr_start)  # TODO: maybe replace the use of A here with some other temporary register?
                    emit_mir(InstrClass.SUB, dst, PhysReg.A)
                else:
                    emit_mir(InstrClass.CONST, PhysReg.A, arr_start)  # TODO: maybe replace the use of A here with some other temporary register?
                    emit_mir(InstrClass.ADD, dst, PhysReg.A)

        return self._instr_replacer(mbb, InstrClass.LEA, replace_lea)

    def legalize_sload(self, mbb):
        def replace_sload(instr, emit_mir):
            dst = instr.operands[0]
            src = instr.operands[1]
            if isinstance(src, Variable):
                emit_mir(InstrClass.CONST, PhysReg.A, src)
            else:
                emit_mir(InstrClass.COPY, PhysReg.A, src)
            emit_mir(InstrClass.LOAD, dst)

        return self._instr_replacer(mbb, InstrClass.SLOAD, replace_sload)

    def legalize_sstore(self, mbb):
        def replace_sstore(instr, emit_mir):
            dst = instr.operands[0]
            src = instr.operands[1]
            if isinstance(dst, Variable):
                emit_mir(InstrClass.CONST, PhysReg.A, dst)
            else:
                emit_mir(InstrClass.COPY, PhysReg.A, dst)
            emit_mir(InstrClass.STORE, src)

        return self._instr_replacer(mbb, InstrClass.SSTORE, replace_sstore)

    def legalize_muldiv(self):
        # Legalization of MUL / DIV requires adding mbbs and changing flow,
        # so it cannot be done via regular replacers

        orig_mbbs = list(self.compilercontext.mbbs.keys())

        # Create a temporary object to handle mbb information
        mbb_handle = Bunch(bbname='', mbb=None)

        def set_mbb(bbname):
            mbb_handle.bbname = bbname
            mbb_handle.mbb = self.compilercontext.mbbs[bbname]

        # Emit a MIR instruction in the current mbb
        def emit_mir(cls, *operands):
            mbb_handle.mbb.append(MIRInstr(cls, operands))
        
        # Emit a jump and fallthorough to the last operand (change mbb)
        def emit_ftjump(cls, *operands):
            mbb_handle.mbb.append(MIRInstr(cls, operands))
            set_mbb(operands[-1])

        for bbname in orig_mbbs:
            orig_mbb = self.compilercontext.mbbs[bbname]
            self.compilercontext.mbbs[bbname] = []
            
            set_mbb(bbname)

            for instr in orig_mbb:
                if instr.cls is InstrClass.MUL:
                    """
                    GET A      # 0
                    GET B      # 1
                    SUB C C    # 2
                    JODD B 8   # 3  jump to ADD A, LOOP
                    HALF B     # 4  RETURN
                    JZERO B 10 # 5  jump to END
                    ADD A A    # 6
                    JUMP 3     # 7  jump to LOOP
                    ADD C A    # 8  ADD A
                    JUMP 4     # 9  jump to RETURN
                    PUT C      # 10 END
                    HALT
                    """
                    mul_loop_bb = self.compilercontext.creatembb('mul_loop')
                    mul_return_bb = self.compilercontext.creatembb('mul_return')
                    mul_jzero_bb = self.compilercontext.creatembb('mul_jzero')
                    mul_adda_bb = self.compilercontext.creatembb('mul_adda')
                    cont_bb = self.compilercontext.creatembb(bbname)

                    vregA = instr.operands[1]
                    vregB = instr.operands[2]
                    vregC = instr.operands[0]

                    emit_mir(InstrClass.SUB, vregC, vregC)
                    emit_ftjump(InstrClass.JUMP, mul_loop_bb)
                    emit_ftjump(InstrClass.SJODD, vregB, mul_adda_bb, mul_return_bb)

                    emit_mir(InstrClass.HALF, vregB)
                    emit_ftjump(InstrClass.SJZERO, vregB, cont_bb, mul_jzero_bb)

                    emit_mir(InstrClass.ADD, vregA, vregA)
                    emit_mir(InstrClass.JUMP, mul_loop_bb)
                    
                    set_mbb(mul_adda_bb)
                    emit_mir(InstrClass.ADD, vregC, vregA)
                    emit_mir(InstrClass.JUMP, mul_return_bb)

                    set_mbb(cont_bb)

                elif instr.cls is InstrClass.DIV:
                    """
                    GET A        # 0
                    GET B        # 1
                    # Handle x/0 and 0/x
                    JZERO A 26   # 2  jump to DIV0a
                    JZERO B 25   # 3  jump to DIV0b
                    SUB C C      # 4
                    # LSH B while it's <= A, count iterations in C
                    # (B - A) <= 0 ==> B <= A
                    COPY D B     # 5  LSHLOOP
                    SUB D A      # 6
                    JZERO D 9    # 7  jump to LSHCONT
                    JUMP 12      # 8  jump to LSHDONE
                    ADD B B      # 9  LSHCONT
                    INC C        # 10
                    JUMP 5       # 11 jump to LSHLOOP
                    # if the C counter is 0, it means that B > A and thus it's an easy case, Q = 0, R = A
                    JZERO C 26   # 12 jump to EZCASE, LSHDONE
                    # D holds quotient (Q)
                    SUB D D      # 13
                    # loop C --> 0
                    # double quotient, half divider
                    HALF B       # 14 LOOPLOOP
                    DEC C        # 15
                    ADD D D      # 16
                    # if B <= A then A-=B, D+=1
                    # (B - A) <= 0 ==> B <= A
                    COPY E B     # 17
                    SUB E A      # 18
                    JZERO E 22   # 19 jump to THEN
                    # end if;
                    JZERO C 27   # 20 jump to FINISHED, ENDIF
                    JUMP 14      # 21 jump to LOOPLOOP
                    # then... block
                    SUB A B      # 22 THEN
                    INC D        # 23
                    JUMP 20      # 24 jump to ENDIF
                    # div0 block
                    SUB A A      # 25 DIV0b
                    SUB D D      # 26 DIV0a, EZCASE (no A setting)
                    # finish
                    PUT D        # 27 FINISHED, print Q
                    PUT A        # 28 print R
                    HALT
                    """
                    div_jzeroa_bb = self.compilercontext.creatembb('div_jzeroa')
                    div_jzerob_bb = self.compilercontext.creatembb('div_jzerob')
                    div_lshloop_bb = self.compilercontext.creatembb('div_lshloop')
                    div_lshcont_bb = self.compilercontext.creatembb('div_lshcont')
                    div_lshdone_bb = self.compilercontext.creatembb('div_lshdone')
                    div_jzeroc_bb = self.compilercontext.creatembb('div_jzeroc')
                    div_looploop_bb = self.compilercontext.creatembb('div_looploop')
                    div_endif_bb = self.compilercontext.creatembb('div_endif')
                    div_then_bb = self.compilercontext.creatembb('div_then')
                    div_div0b_bb = self.compilercontext.creatembb('div_div0b')
                    div_div0a_bb = self.compilercontext.creatembb('div_div0a')

                    cont_bb = self.compilercontext.creatembb(bbname)

                    vregA = instr.operands[0]
                    vregB = instr.operands[1]
                    vregC = instr.operands[2]
                    vregD = instr.operands[3]
                    vregE = instr.operands[4]

                    # JZERO A 26   # 2  jump to DIV0a
                    emit_ftjump(InstrClass.SJZERO, vregA, div_div0a_bb, div_jzeroa_bb)
                    # JZERO B 25   # 3  jump to DIV0b
                    emit_ftjump(InstrClass.SJZERO, vregB, div_div0b_bb, div_jzerob_bb)
                    # SUB C C      # 4
                    emit_mir(InstrClass.SUB, vregC, vregC)
                    # # LSH B while it's <= A, count iterations in C
                    # # (B - A) <= 0 ==> B <= A
                    emit_ftjump(InstrClass.JUMP, div_lshloop_bb)
                    # COPY D B     # 5  LSHLOOP
                    emit_mir(InstrClass.COPY, vregD, vregB)
                    # SUB D A      # 6
                    emit_mir(InstrClass.SUB, vregD, vregA)
                    # JZERO D 9    # 7  jump to LSHCONT
                    # JUMP 12      # 8  jump to LSHDONE
                    emit_mir(InstrClass.SJZERO, vregD, div_lshcont_bb, div_lshdone_bb)
                    set_mbb(div_lshcont_bb)
                    # ADD B B      # 9  LSHCONT
                    emit_mir(InstrClass.ADD, vregB, vregB)
                    # INC C        # 10
                    emit_mir(InstrClass.INC, vregC)
                    # JUMP 5       # 11 jump to LSHLOOP
                    emit_mir(InstrClass.JUMP, div_lshloop_bb)
                    # # if the C counter is 0, it means that B > A and thus it's an easy case, Q = 0, R = A
                    set_mbb(div_lshdone_bb)
                    # JZERO C 26   # 12 jump to EZCASE, LSHDONE
                    emit_ftjump(InstrClass.SJZERO, vregC, div_div0a_bb, div_jzeroc_bb)
                    # # D holds quotient (Q)
                    # SUB D D      # 13
                    emit_mir(InstrClass.SUB, vregD, vregD)
                    # # loop C --> 0
                    # # double quotient, half divider
                    emit_ftjump(InstrClass.JUMP, div_looploop_bb)
                    # HALF B       # 14 LOOPLOOP
                    emit_mir(InstrClass.HALF, vregB)
                    # DEC C        # 15
                    emit_mir(InstrClass.DEC, vregC)
                    # ADD D D      # 16
                    emit_mir(InstrClass.ADD, vregD, vregD)
                    # # if B <= A then A-=B, D+=1
                    # # (B - A) <= 0 ==> B <= A
                    # COPY E B     # 17
                    emit_mir(InstrClass.COPY, vregE, vregB)
                    # SUB E A      # 18
                    emit_mir(InstrClass.SUB, vregE, vregA)
                    # JZERO E 22   # 19 jump to THEN
                    emit_ftjump(InstrClass.SJZERO, vregE, div_then_bb, div_endif_bb)
                    # # end if;
                    # JZERO C 27   # 20 jump to FINISHED, ENDIF
                    # JUMP 14      # 21 jump to LOOPLOOP
                    emit_mir(InstrClass.SJZERO, vregC, cont_bb, div_looploop_bb)
                    # # then... block
                    set_mbb(div_then_bb)
                    # SUB A B      # 22 THEN
                    emit_mir(InstrClass.SUB, vregA, vregB)
                    # INC D        # 23
                    emit_mir(InstrClass.INC, vregD)
                    # JUMP 20      # 24 jump to ENDIF
                    emit_mir(InstrClass.JUMP, div_endif_bb)
                    # # div0 block
                    set_mbb(div_div0b_bb)
                    # SUB A A      # 25 DIV0b
                    emit_mir(InstrClass.SUB, vregA, vregA)
                    emit_ftjump(InstrClass.JUMP, div_div0a_bb)
                    # SUB D D      # 26 DIV0a, EZCASE (no A setting)
                    emit_mir(InstrClass.SUB, vregD, vregD)
                    # # finish
                    emit_ftjump(InstrClass.JUMP, cont_bb)

                else:  # Rewrite all the other instructions
                    mbb_handle.mbb.append(instr)


class ISel:
    def __init__(self, compilercontext):
        self.compilercontext = compilercontext
        self.tmpvar = Variable.get('R')  # An artificial variable for temporary values
        self.defuseanal  = compilercontext.get_analysis(DefUseAnalysis, False)

    def process_block(self, bb):
        mbb = []

        def emit_mir(cls, *operands):
            vreg_operands = tuple(VirtReg.get(op.name)
                                  if isinstance(op, IRValue)
                                  else op
                                  for op in operands)
            mbb.append(MIRInstr(cls, vreg_operands))
        
        def next_tmpvreg():
            tmpvar = self.tmpvar.nextirvar()
            return VirtReg.get(tmpvar)

        for instr in bb:
            # For all the regular IRInstr, simply create a MIRInstr copy
            if not isinstance(instr, IRValue):
                emit_mir(instr.cls, *instr.operands)
            # For the others, there are specialized implementations
            elif instr.cls is InstrClass.LOAD:
                emit_mir(instr.cls, instr)
            elif instr.cls is InstrClass.GET or instr.cls is InstrClass.NOPDEF:
                emit_mir(instr.cls, instr)
                emit_mir(InstrClass.NOPUSE, instr)  # A no-op use to ensure GET is not removed by DCE
            elif instr.cls is InstrClass.ADD:
                emit_mir(InstrClass.COPY, instr, instr.operands[0])
                if instr.operands[1].cls is InstrClass.CONST and instr.operands[1].operands[0] < ConstPropagation.max_const_incdec:
                    for _ in range(instr.operands[1].operands[0]):
                        emit_mir(InstrClass.INC, instr)
                else:
                    emit_mir(InstrClass.ADD, instr, instr.operands[1])
            elif instr.cls is InstrClass.SUB:
                emit_mir(InstrClass.COPY, instr, instr.operands[0])
                if instr.operands[1].cls is InstrClass.CONST and instr.operands[1].operands[0] < ConstPropagation.max_const_incdec:
                    for _ in range(instr.operands[1].operands[0]):
                        emit_mir(InstrClass.DEC, instr)
                else:
                    emit_mir(InstrClass.SUB, instr, instr.operands[1])
            elif instr.cls is InstrClass.MUL:
                tmpvreg0 = next_tmpvreg()
                tmpvreg1 = next_tmpvreg()
                emit_mir(InstrClass.COPY, tmpvreg0, instr.operands[0])
                emit_mir(InstrClass.COPY, tmpvreg1, instr.operands[1])
                emit_mir(InstrClass.NOPDEF, instr)
                emit_mir(instr.cls, instr, tmpvreg0, tmpvreg1)
            elif instr.cls is InstrClass.DIV:
                done=False
                if instr.operands[1].cls is InstrClass.CONST:
                    # If div is by a const power of 2, change to shift
                    val = instr.operands[1].operands[0]
                    if (val & (val - 1)) == 0:
                        log2 = len(bin(val)) - 3
                        emit_mir(InstrClass.COPY, instr, instr.operands[0])
                        for _ in range(log2):
                            emit_mir(InstrClass.HALF, instr)
                        done=True

                if not done:
                    tmpvreg0 = next_tmpvreg()
                    tmpvreg1 = next_tmpvreg()
                    tmpvreg2 = next_tmpvreg()
                    tmpvreg3 = next_tmpvreg()
                    emit_mir(InstrClass.COPY, tmpvreg0, instr.operands[0])
                    emit_mir(InstrClass.COPY, tmpvreg1, instr.operands[1])
                    emit_mir(InstrClass.NOPDEF, tmpvreg2)
                    emit_mir(InstrClass.NOPDEF, tmpvreg3)
                    emit_mir(InstrClass.NOPDEF, instr)
                    emit_mir(InstrClass.DIV, tmpvreg0, tmpvreg1, tmpvreg2, instr, tmpvreg3)
            elif instr.cls is InstrClass.REM:
                done=False
                if instr.operands[1].cls is InstrClass.CONST:
                    val = instr.operands[1].operands[0]
                    if (val & (val - 1)) == 0:
                        log2 = len(bin(val)) - 3
                        tmpvreg0 = next_tmpvreg()
                        emit_mir(InstrClass.COPY, instr, instr.operands[0])
                        emit_mir(InstrClass.COPY, tmpvreg0, instr.operands[0])
                        for _ in range(log2):
                            emit_mir(InstrClass.HALF, tmpvreg0)
                        for _ in range(log2):
                            emit_mir(InstrClass.ADD, tmpvreg0, tmpvreg0)
                        emit_mir(InstrClass.SUB, instr, tmpvreg0)
                        done=True

                if not done:
                    tmpvreg0 = next_tmpvreg()
                    tmpvreg1 = next_tmpvreg()
                    tmpvreg2 = next_tmpvreg()
                    tmpvreg3 = next_tmpvreg()
                    emit_mir(InstrClass.COPY, instr, instr.operands[0])
                    emit_mir(InstrClass.COPY, tmpvreg0, instr.operands[1])
                    emit_mir(InstrClass.NOPDEF, tmpvreg1)
                    emit_mir(InstrClass.NOPDEF, tmpvreg2)
                    emit_mir(InstrClass.NOPDEF, tmpvreg3)
                    emit_mir(InstrClass.DIV, instr, tmpvreg0, tmpvreg1, tmpvreg2, tmpvreg3)
            elif instr.cls is InstrClass.INC or instr.cls is InstrClass.DEC or \
                instr.cls is InstrClass.HALF:
                emit_mir(InstrClass.COPY, instr, instr.operands[0])
                emit_mir(instr.cls, instr)
            elif instr.cls is InstrClass.SLOAD or instr.cls is InstrClass.CONST:
                emit_mir(instr.cls, instr, instr.operands[0])
            elif instr.cls is InstrClass.LEA:
                if instr.operands[1].cls is InstrClass.CONST:
                    emit_mir(instr.cls, instr, instr.operands[0], instr.operands[1].operands[0])
                else:
                    emit_mir(instr.cls, instr, *instr.operands)
            elif instr.cls is InstrClass.PHI:
                emit_mir(instr.cls, instr, {bb: var and VirtReg.get(var.name) for bb, var in instr.operands[1].items()})
            elif instr.cls is InstrClass.COPY:  # < Um, actually COPY instr should be eliminated
                print(f"WARNING: Copy instruction not eliminated: {instr}")
                emit_mir(instr.cls, instr, *instr.operands)
            else:
                raise CompilerError(f"Unprocessed variable: {instr}")

        return mbb

    def phi_elimination(self, mbb):
        """
        PHI Node elimination. Replaces PHI Nodes with copies in their predecessors.
        Must be ran after all blocks have been processed.
        """
        while mbb[0].cls is InstrClass.PHI:
            vreg, vdict = mbb[0].operands
            print(f"Eliminating PHI Node: {mbb[0]}")

            for pre, src in vdict.items():
                if src is not None:
                    new_instr = MIRInstr(InstrClass.COPY, (vreg, src))
                else:  # For undef sources, insert NOPDEF to constraint life range
                    new_instr = MIRInstr(InstrClass.NOPDEF, (vreg,))
                # The last instruction of the pre must be a terminator, so insert into one before
                self.compilercontext.mbbs[pre][-1:-1] = [new_instr]
            
            del mbb[0]


class RegAlloc:
    def __init__(self, compilercontext):
        self.compilercontext = compilercontext

        # Results of external cfg and def-use analysis
        self.cfganal = None
        self.defuseanal = None

        # Results of the per-block allocation step, applied at the post-processing step
        self.allocation = {}

        # Results of interference analysis
        self.interferences = None

        # Record of all SpillSlots
        self.spillslots = set()

        self.tmpvar = Variable.get('S')
    
    def invalidate(self):
        # Results of the per-block allocation step, applied at the post-processing step
        self.allocation = {}

        # Results of interference analysis
        self.interferences = None
    
    class SpillSlot:
        count = 0

        def __init__(self):
            self.number = self.count
            type(self).count += 1
            self.variable = None
        
        def __repr__(self):
            return '^{}'.format(self.number)

    def get_spill_slot(self):
        ss = self.SpillSlot()
        self.spillslots.add(ss)
        return ss
    
    def ra_legalize(self):
        """
        This function checks if every vreg that has at least 1 def has at least 1 use.
        If not, if the vreg is def-fed by protected instr, a NOPUSE is added;
        all the non-protected def instructions are removed.
        """

        instr_patch = []

        mbbaugs = self.defuseanal.mbbaugs
        for vreg in self.defuseanal.all_regs:
            def_instrs = []
            use_count = 0

            for bbname, mbbaug in mbbaugs.items():
                if vreg in self.defuseanal.block_regs[bbname]:
                    for idx, (instr, mir_defs, mir_uses) in enumerate(mbbaug):
                        if vreg in mir_defs:
                            def_instrs.append((bbname, idx, instr))
                        if vreg in mir_uses:
                            use_count += 1
            
            if use_count == 0:
                for bbname, idx, instr in def_instrs:
                    if instr.cls.isprotected:
                        instr_patch.append((True, bbname, idx+1, MIRInstr(InstrClass.NOPUSE, (vreg,))))
                    else:
                        instr_patch.append((False, bbname, idx, instr))
        
        # TODO: let apply_instruction_patch patch remove instructions as well, then refactor this to use apply_instruction_patch
        for bbname, mbb in self.compilercontext.mbbs.items():
            bb_patch = [(add, idx, instr) for add, ibbname, idx, instr in instr_patch if ibbname == bbname]
            bb_patch.sort(key=lambda x: x[1], reverse=True)
            for add, idx, instr in bb_patch:
                assert 0 <= idx < len(mbb)
                if add:
                    mbb[idx:idx] = [instr]
                    print(f"Applied patch: {mbb[idx]} at {idx} in {bbname}")
                else:
                    print(f"Removed instruction: {mbb[idx]} at {idx} in {bbname} ({instr})")
                    del mbb[idx]
            
            # If any instruction patch has been applied, invalidate DefUseAnalysis for the block
            if bb_patch:
                self.invalidate(bbname=bbname)
        
        return bool(instr_patch)
    
    def insert_split(self, bbname, range_idx, vreg):
        """
        This function identifies all defs and uses for vreg at the position range_idx in
        `bbname`. For each def, all next-uses are identified, and consequently, for each use, all last-defs.
        Finally, at each def, a COPY to a new temporary vreg is issued, and each use is prepended with a 
        COPY from the vreg.
        """
        tmpvar = self.tmpvar.nextirvar()
        tmpreg = VirtReg.get(tmpvar)
        spill_defs, spill_uses = self.spill_split_impl(bbname, range_idx, vreg)

        instr_to_add = [
            (bbname, idx+1, MIRInstr(InstrClass.COPY, (tmpreg, vreg)))
            for bbname, idx in spill_defs
        ] + [
            (bbname, idx, MIRInstr(InstrClass.COPY, (vreg, tmpreg)))
            for bbname, idx in spill_uses
        ]

        pprint(instr_to_add)

        return instr_to_add
        
    def insert_spill(self, bbname, range_idx, vreg):
        """
        This function identifies all defs and uses for vreg at the position range_idx in
        `bbname`. For each def, all next-uses are identified, and consequently, for each use, all last-defs.
        Finally, at each def, a SSTORE to a new spill slot is issued, and each use is prepended with a reload.
        """
        slot = self.get_spill_slot()
        spill_defs, spill_uses = self.spill_split_impl(bbname, range_idx, vreg)

        instr_to_add = [
            (bbname, idx+1, MIRInstr(InstrClass.SSTORE, (slot, vreg)))
            for bbname, idx in spill_defs
        ] + [
            (bbname, idx, MIRInstr(InstrClass.SLOAD, (vreg, slot)))
            for bbname, idx in spill_uses
        ]

        pprint(instr_to_add)

        return instr_to_add

    def spill_split_impl(self, bbname, range_idx, vreg):
        bbdict = self.compilercontext.mbbs

        spill_defs = set()
        spill_uses = set()

        visited = [set()]

        def identify_all_defs(bbstart, bbidx, reset=False):
            """ This function iteratively/recursively tries to identify all defs
            that affect vreg at bbidx in bbstart """
            if reset:
                visited[0] = set()
            
            try:
                ldef = self.defuseanal.last_defs[bbstart][vreg][bbidx]
            except KeyError:
                return set()

            all_defs = set()
            if ldef == -1:
                for pre in self.cfganal.predecessors[bbstart]:
                    if pre not in visited[0]:
                        visited[0].add(pre)

                        all_defs |= identify_all_defs(pre, len(bbdict[pre]))
            else:
                all_defs.add((bbstart, ldef))
            return all_defs

        def identify_all_uses(bbstart, bbidx, reset=False):
            """ This function iteratively/recursively tries to identify all uses
            that follow vreg at bbidx in bbstart """
            if reset:
                visited[0] = set()
            
            try:
                nuse = self.defuseanal.next_uses[bbstart][vreg][bbidx]
            except KeyError:
                return set()

            all_uses = set()
            if nuse == len(bbdict[bbstart]):
                for suc in self.cfganal.successors[bbstart]:
                    if suc not in visited[0]:
                        visited[0].add(suc)

                        all_uses |= identify_all_uses(suc, -1)
            else:
                all_uses.add((bbstart, nuse))
            return all_uses


        # First, identify the defs for the spill.
        
        spill_defs = identify_all_defs(bbname, range_idx, True)

        # Now, in loop, for all defs find all uses and for all uses, all defs, until nothing changes
        frozen_hashes = (None, None)
        next_hashes = (frozen_hash(spill_defs), frozen_hash(spill_uses))
        while frozen_hashes != next_hashes:
            frozen_hashes = next_hashes

            for ldef in spill_defs:
                spill_uses |= identify_all_uses(ldef[0], ldef[1]+1, True)

            for nuse in spill_uses:
                spill_defs |= identify_all_defs(nuse[0], nuse[1]-1, True)
            
            next_hashes = (frozen_hash(spill_defs), frozen_hash(spill_uses))

        # Validate none of the spills is placed after a SJZERO/SJODD
        spill_defs = {
            (bbname, idx-1)
            if bbdict[bbname][idx].cls is InstrClass.SJZERO or bbdict[bbname][idx].cls is InstrClass.SJODD else
            (bbname, idx)
            for bbname, idx in spill_defs
        }

        # Now, for each spill def, issue a spill store and for each spill use, spill reload
        print("SPILLS:")
        pprint(spill_defs)
        print("RELOADS:")
        pprint(spill_uses)

        return spill_defs, spill_uses

    def vreg_splitting(self):
        """
        For each vreg, and each block that uses/defs it, scan for life-range "islands", i.e.
        Parts that are separated by Nones in next_use graphs. Note, this has to take into account
        possible successors. When it turns out that a vreg has multiple "islands", assign a separate
        vreg for each such "island".
        """
        bbdict = self.compilercontext.mbbs
        changed = False

        all_vregs = {reg for reg in self.defuseanal.all_regs if isinstance(reg, VirtReg)}
        for reg in all_vregs:
            color = -1
            next_unique = 0
            color_mapping = {}
            instr_mapping = {}
            for bbname, bb in bbdict.items():
                if reg in self.defuseanal.block_regs[bbname]:
                    # First, check if block predecessors are already colored at their "export" instruction
                    predecessor_colors = [instr_mapping[(pre, len(bbdict[pre]))] for pre in self.cfganal.predecessors[bbname] if (pre, len(bbdict[pre])) in instr_mapping]
                    if predecessor_colors:
                        # If there is only one color, use it. Otherwise, use the first one, and recolor all other predecessors to the color
                        color, *others = sorted(list(set(predecessor_colors)))
                        for other in others:
                            for iidx in color_mapping[other]:
                                instr_mapping[iidx] = color
                            color_mapping[color] += color_mapping[other]
                            del color_mapping[other]
                    # If not, use the next unique color
                    else:
                        color = next_unique
                        next_unique += 1
                    
                    next_use = self.defuseanal.next_uses[bbname][reg]
                    last_def = self.defuseanal.last_defs[bbname][reg]
                    is_alive_at = lambda idx: next_use[idx] is not None or last_def[idx] == idx

                    color_fresh = True
                    for idx in range(len(bb)+1):
                        if is_alive_at(idx):
                            color_fresh = False
                            iidx = (bbname, idx)
                            try:
                                color_mapping[color].append(iidx)
                            except KeyError:
                                color_mapping[color] = [iidx]
                            instr_mapping[iidx] = color
                        else:
                            if not color_fresh:
                                color_fresh = True
                                color = next_unique
                                next_unique += 1
                    
                    # If the register is alive at the last index, check if successors have already computed imports.
                    # If so, recolor all the imports to the current color
                    if not color_fresh:
                        for suc in self.cfganal.successors[bbname]:
                            successor_colors = {instr_mapping[(suc, 0)] for suc in self.cfganal.successors[bbname] if (suc, 0) in instr_mapping}
                            for other in successor_colors:
                                if other != color:
                                    for iidx in color_mapping[other]:
                                        instr_mapping[iidx] = color
                                    color_mapping[color] += color_mapping[other]
                                    del color_mapping[other]

            # If there is more than 1 color used, rename the registers
            if len(color_mapping) > 1:
                changed = True

                for color, instrlist in color_mapping.items():
                    new_reg = VirtReg.get(f"{reg.name}#{color}")

                    print(f"Replacing an island of {reg} with {new_reg}")

                    for bbname, idx in instrlist:
                        bb = bbdict[bbname]
                        if idx < len(bb):
                            if reg in bb[idx].operands:
                                print(f"Replacing at {bbname}:{idx} {bb[idx]}")
                                bb[idx].operands = tuple(new_reg if op == reg else op for op in bb[idx].operands)
                        
        if changed:
            # TODO: how to reduce # of invalidates here?
            self.cfganal.invalidate(bbname=bbname)

        return changed
    
    def life_range_splitting(self, bbname, mbbaug):
        """
        For each block, iterate instructions and look for places, where there are more
        than 7 alive registers at the same moment. For each such, find the longest unused
        interval and split it by adding SSTORE after the last def and SLOAD before the next use.

        Returns as soon as a set of instruction to add are identified.
        If no such set is identified, the function returns None.
        """
        
        next_use = self.defuseanal.next_uses[bbname]
        last_def = self.defuseanal.last_defs[bbname]
        regs = self.defuseanal.block_regs[bbname]

        for idx, (instr, mir_defs, mir_uses) in enumerate(mbbaug):
            alive_regs = [reg for reg in regs if isinstance(reg, VirtReg) and next_use[reg][idx] is not None]
            concurrent_alive = len(alive_regs)
            if concurrent_alive > 7:
                print(f"Too many alive registers in {bbname}@{idx}.")
                lr_len = [(reg, next_use[reg][idx] - last_def[reg][idx]) for reg in alive_regs]
                print("Computed life range skips:")
                pprint(lr_len)

                # Select the longest skip in life range
                longest = max(lr_len, key=lambda x: x[1])

                print(f"Selected longest interval: {longest}")
                # Add SSTORE just after the last_def and SLOAD before the next_use
                reg = longest[0]
                return self.insert_spill(bbname, idx, reg)
        
        return None
    
    def split_longest_interval(self):
        """
        This function selects the vreg with the most interferences,
        selects the longest "inactive" interval across its "active" ranges,
        and creates a "spill" to a temporary vreg (insert 2 copies)
        TODO: since blindly insering splits seems to only make this worse on large ranges,
        for now replaced split with a spill.
        """
        reg, _ = max(self.interferences.items(), key=lambda x: len(x[1]))

        lr_len = [(bbname, idx, next_use[reg][idx] - last_def[reg][idx]) 
                  for bbname, mbb in self.compilercontext.mbbs.items()
                  if reg in self.defuseanal.block_regs[bbname]
                  for next_use in (self.defuseanal.next_uses[bbname],)
                  for last_def in (self.defuseanal.last_defs[bbname],)
                  for idx in range(len(mbb))
                  if next_use[reg][idx] is not None
                  and last_def[reg][idx] is not None ]
        
        max_split = max(lr_len, key=lambda x: x[2])

        pprint(lr_len)
        print(f"Max split: {max_split}")

        # TODO: see docstring
        #return self.insert_split(max_split[0], max_split[1], reg)
        return self.insert_spill(max_split[0], max_split[1], reg)

    def analyze_interferences(self):
        # For each virt register, record its interference: all registers that are used at the same time
        self.interferences = {
            reg: set(
                oth
                for bbname, mbb in self.compilercontext.mbbs.items()
                if reg in self.defuseanal.block_regs[bbname]
                for idx, _ in enumerate(mbb)
                if self.defuseanal.next_uses[bbname][reg][idx] is not None
                for oth in self.defuseanal.block_regs[bbname]
                if self.defuseanal.next_uses[bbname][oth][idx] is not None
                and oth is not reg
                and isinstance(oth, VirtReg)
            )
            for reg in self.defuseanal.all_regs
            if isinstance(reg, VirtReg)
        }

        print("> Interferences:")
        pprint(self.interferences)
    
    def apply_instruction_patch(self, patch):
        for bbname, mbb in self.compilercontext.mbbs.items():
            bb_patch = [(idx, instr) for ibbname, idx, instr in patch if ibbname == bbname]
            bb_patch.sort(key=lambda x: x[0], reverse=True)
            for idx, instr in bb_patch:
                assert 0 <= idx < len(mbb), f"Invalid instruction patch: {bbname}:{idx} {instr}"
                mbb[idx:idx] = [instr]
                print(f"Applied patch: {mbb[idx]} at {idx} in {bbname}")
            
            # If any instruction patch has been applied, invalidate DefUseAnalysis for the block
            if bb_patch:
                self.cfganal.invalidate(bbname=bbname)

    def rewrite_bb(self, bbname, mbb):
        for instr in mbb:
            instr.operands = tuple(self.allocation[op] if isinstance(op, VirtReg) else
                                   op.memloc if isinstance(op, self.SpillSlot) else
                                   op for op in instr.operands)

    def process(self):
        did_modify = True

        self.defuseanal = self.compilercontext.get_analysis(DefUseAnalysis, True)
        self.cfganal = self.compilercontext.get_analysis(CFGAnalysis, True)

        bbdict = self.compilercontext.mbbs

        while did_modify:
            did_modify = False

            self.defuseanal.validate(bbdict)
            self.cfganal.validate(bbdict)  # < this should never have to be re-validated here, but just in case...

            if self.ra_legalize():
                did_modify = True
                self.invalidate()
                print(">>>> RA After-legalize")
                self.compilercontext.dump_mir()
                print("<<<< RA After-legalize")
                continue

            if self.vreg_splitting():
                did_modify = True
                self.invalidate()
                print(">>>> RA After-split")
                self.compilercontext.dump_mir()
                print("<<<< RA After-split")
                continue

            for bbname, mbbaug in self.defuseanal.mbbaugs.items():
                t = self.life_range_splitting(bbname, mbbaug)
                if t is not None:
                    self.apply_instruction_patch(t)
                    did_modify = True
                    self.invalidate()
                    print(">>>> RA After-split")
                    self.compilercontext.dump_mir()
                    print("<<<< RA After-split")
                    break
            
            if did_modify:
                continue
            
            self.analyze_interferences()
        
            # Naive implementation - try to color a graph
            if not self.try_graph_coloring():
                # If it fails, split the longest interval and rerun everything.
                t = self.split_longest_interval()
                self.apply_instruction_patch(t)

                did_modify = True
                continue
        
        print("Allocation succeeded. Results:")
        pprint(self.allocation)

        # Validating allocation:
        for vreg in self.defuseanal.all_regs:
            if isinstance(vreg, VirtReg):
                for i in self.interferences[vreg]:
                    assert self.allocation[i] is not self.allocation[vreg]
        
        # Assign spill slots
        # TODO: do this via coloring, this will require another interference pass etc,
        # but there is potentially unlimited number of spill slots so...
        for ss in self.spillslots:
            # Naive assignment
            ss.memloc = Variable.get(f'S${ss.number}')

        # REWRITE: replace all vregs in operands with physregs
        # and all spill slots with their memlocs
        for bbname, mbb in self.compilercontext.mbbs.items():
            self.rewrite_bb(bbname, mbb)
        
        # Post-RA, invalidate all
        self.defuseanal.invalidate()

    class BacktrackingTimeout(Exception):
        pass
    
    def try_graph_coloring(self):
        regs = list(reg for reg in self.defuseanal.all_regs if isinstance(reg, VirtReg))
        regs.sort(key=lambda x: len(self.interferences[x]))
        physregs = list(PhysReg(i) for i in range(1, 8))

        # First, try greedy algorithm on a sorted register list
        try:
            print(f"Trying greedy coloring for reg list {regs}")
            self.greedy_coloring(regs, physregs, self.allocation, self.interferences)

            return True
        except NotImplementedError:  # < TODO: new exception here, add option to throw or else...
            # If it failed, reset allocation and try the backtracking algorithm
            print(f"Greedy allocation failed, fall-back to backtracking")

            self.allocation = {}

            done = False
            while True:
                try:
                    print(f"Trying backtracking coloring for reg list {regs}")
                    done = self.backtracking_coloring(regs, physregs, self.allocation, self.interferences)
                    return done
                except self.BacktrackingTimeout:
                    print("... Timed out. Shuffling...")
                    random.shuffle(regs)

    def backtracking_coloring(self, vertices, colors, allocation, graph, timeout=100000):
        to_do = collections.deque(vertices)
        is_color_ok = lambda v, c: all(allocation[r] is not c for r in graph[v] if r in allocation)

        timeout = [timeout]

        def recursive_scan(v):
            if timeout[0] <= 0:
                raise self.BacktrackingTimeout()
            
            timeout[0] -= 1

            for c in colors:
                if is_color_ok(v, c):
                    allocation[v] = c

                    if not to_do:
                        return True
                    
                    next = to_do.pop()

                    if recursive_scan(next):
                        return True
                    
                    to_do.append(next)
                    del allocation[v]
            
            return False
        
        return recursive_scan(to_do.pop())

    def greedy_coloring(self, vertices, colors, allocation, graph):
        to_do = collections.deque(vertices)
        # Assign the first color to first vertex
        first = to_do.pop()
        allocation[first] = colors[0]

        print(f'Allocated {first} in {allocation[first]}')
        # Assign colors to remaining vertices 
        while to_do:
            reg = to_do.pop()

            # A temporary array to mark which slots are available.
            available = set(colors)

            # Process all adjacent vertices and flag their colors 
            # as unavailable 
            for n in graph[reg]:
                if n in allocation:
                    available -= {allocation[n]}
  
            # Find the first available color
            if not available:
                # TODO: ran out of colors!
                # TODO: life-range splitting?
                raise NotImplementedError

            color, *_ = sorted(available)

            allocation[reg] = color  # Assign the found color 
            print(f'Allocated {reg} in {color}')


class Analysis:
    def __init__(self, compilercontext, is_machine):
        self.compilercontext = compilercontext
        self.is_machine = is_machine
    
    def analyze(self, bbdict):
        """
        Perform analysis. bbdict is either bbs or mbbs, depending on whether the analysis is IR-based or MIR-based
        """
        raise NotImplementedError

    @property
    def valid(self):
        """
        Check if analysis is valid. Return True if it's valid for all basic blocks, False otherwise
        """
        raise NotImplementedError
    
    def invalidate(self):
        """
        Invalidate analysis.
        This function may override with different parameters, such as block, but shall
        provide a default values for each of them. E.g., there may be a "bbname" parameter, but it should default
        to None for all basic blocks.
        """
        raise NotImplementedError
    
    def validate(self, bbdict):
        """
        Recompute the whole analysis, or a specific part of it. 
        This function may override with different parameters, such as block, but shall
        provide a default values for each of them. E.g., there may be a "bbname" parameter, but it should default
        to None for all basic blocks.
        """
        raise NotImplementedError


class CFGAnalysis(Analysis):
    def __init__(self, compilercontext, is_machine):
        super().__init__(compilercontext, is_machine)
        self.predecessors = None
        self.successors = None
        self.valid_for = {}

    def analyze(self, bbdict):
        # For each bb find the bbs that precede and succeede it
        cfg_pre = { bb: set() for bb in bbdict.keys() }
        cfg_suc = { bb: set() for bb in bbdict.keys() }

        self.valid_for = {}

        for bbname, bb in bbdict.items():
            for instr in bb:
                if instr.cls is InstrClass.JUMP:
                    dst = instr.operands[0]
                    cfg_suc[bbname].add(dst)
                    cfg_pre[dst].add(bbname)
                elif instr.cls is InstrClass.JZERO or instr.cls is InstrClass.JODD:
                    dst = instr.operands[1]
                    cfg_suc[bbname].add(dst)
                    cfg_pre[dst].add(bbname)
                elif instr.cls is InstrClass.SJZERO or instr.cls is InstrClass.SJODD:
                    dst0 = instr.operands[1]
                    dst1 = instr.operands[2]
                    cfg_suc[bbname].add(dst0)
                    cfg_suc[bbname].add(dst1)
                    cfg_pre[dst0].add(bbname)
                    cfg_pre[dst1].add(bbname)
            
            self.valid_for[bbname] = True

        self.predecessors = cfg_pre
        self.successors = cfg_suc
    
    @property
    def valid(self):
        # Give up, if no valid_for entries
        if not self.valid_for:
            return False
        
        # If valid for all entries inside, return true
        return all(valid for valid in self.valid_for.values())
    
    def invalidate(self, bbname=None):
        if bbname is None:
            self.valid_for.clear()
            self.predecessors = None
            self.successors = None
        else:
            try:
                self.valid_for[bbname] = False
                del self.predecessors[bbname]
                del self.successors[bbname]
            except KeyError:
                pass
    
    def validate(self, bbdict):
        # TODO: single-block validation
        if not self.valid:
            self.analyze(bbdict)

class DefUseAnalysis(Analysis):
    # This allows for different classes to actually be "analyzable", i.e. not only
    # vregs, but also physregs or spill slots
    mir_analyzable = (VirtReg, PhysReg, RegAlloc.SpillSlot)

    def __init__(self, compilercontext, is_machine=True):
        super().__init__(compilercontext, is_machine)

        # Use for caching valid bblocks (TODO)
        self.valid_for = {}

        if is_machine:
            # Analysis results for MIR variant
            self.mbbaugs = {}
            self.next_uses = {}
            self.last_defs = {}

            self.all_regs = set()
            self.block_regs = {}
            
            # Specialize analysis function
            self.analyze = self.analyze_mbbs

        else:
            # Analysis results for IR variant
            self.use_lookup = {}
            self.def_lookup = {}

            # Specialize analysis function
            self.analyze = self.analyze_bbs

        self.is_machine = is_machine

    @property
    def valid(self):
        # Give up, if no valid_for entries
        if not self.valid_for:
            return False
        
        # If valid for all entries inside, return true
        return all(valid for valid in self.valid_for.values())
    
    def invalidate(self, reg=None):
        # Per-register is only applicable for MIR
        if self.is_machine:
            # TODO: investigate which invalidates make sense here... reg? bbname?
            if reg is None:
                self.valid_for.clear()
            
                self.mbbaugs = {}
                self.next_uses = {}
                self.last_defs = {}

                self.all_regs = set()
                self.block_regs = {}
            else:
                pass
                # TODO
                self.valid_for.clear()
            
                self.mbbaugs = {}
                self.next_uses = {}
                self.last_defs = {}

                self.all_regs = set()
                self.block_regs = {}
        else:
            self.valid_for.clear()
            self.use_lookup = {}
            self.def_lookup = {}
            
    def validate(self, bbdict):
        # TODO: single-block validation
        if not self.valid:
            self.analyze(bbdict)
    
    def analyze_bbs(self, bbdict):
        use_lookup = {}
        def_lookup = {}
        for bbname, bb in bbdict.items():
            for idx, instr in enumerate(bb):
                def_lookup[instr] = (bbname, idx)

                if instr.cls is InstrClass.PHI:
                    phimap = instr.operands[1]

                    for src, val in phimap.items():
                        if isinstance(val, IRValue):
                            x = (instr, src)
                            try:
                                use_lookup[val].add(x)
                            except KeyError:
                                use_lookup[val] = {x}
                    
                else:
                    for opidx, op in enumerate(instr.operands):
                        if isinstance(op, IRValue):
                            x = (instr, opidx)
                            try:
                                use_lookup[op].add(x)
                            except KeyError:
                                use_lookup[op] = {x}

        self.use_lookup = use_lookup
        self.def_lookup = def_lookup

    def analyze_mbbs(self, bbdict, regs=None):
        # Get result of a CFG analysis
        self.cfganal = self.compilercontext.get_analysis(CFGAnalysis, True)

        # Prepare mbbaugs
        self.mbbaugs = {}
        for bbname, mbb in bbdict.items():
            self.mbbaugs[bbname] = [
                (instr,
                 {instr.operands[r]
                  for r in instr.cls.mir_def
                  if isinstance(instr.operands[r], self.mir_analyzable)},
                 {instr.operands[r]
                  for r in instr.cls.mir_use
                  if isinstance(instr.operands[r], self.mir_analyzable)})
                for instr in mbb
            ]
        
        # Iterate mbbaugs and extract all regs
        self.all_regs = {reg
                         for mbbaug in self.mbbaugs.values()
                         for instr, mir_defs, mir_uses in mbbaug
                         for reg in (mir_defs | mir_uses)}
        
        # Find all HALT blocks, which we use for tracking required defs
        halt_blocks = [bbname for bbname, mbb in bbdict.items() if mbb[-1].cls is InstrClass.HALT]
        
        # For full processing, ensure the next_uses and last_defs are clean
        self.next_uses = {}
        self.last_defs = {}

        # Perform analysis for each register:
        for reg in self.all_regs:
            self.trace_register(halt_blocks, reg)
        
        # After that, split the next_uses (x,y,z) into layers [x][y][z]
        self.next_uses = {
            bbname: {
                reg: {
                    idx: self.next_uses[(bbname, reg, idx)] 
                    for idx in range(-1, len(mbb)+1)
                }
                for reg in self.all_regs
            }
            for bbname, mbb in bbdict.items()
        }
        self.last_defs = {
            bbname: {
                reg: {
                    idx: self.last_defs[(bbname, reg, idx)] 
                    for idx in range(-1, len(mbb)+1)
                }
                for reg in self.all_regs
            }
            for bbname, mbb in bbdict.items()
        }

        # Finally, for each block, for each reg, remove the reg if it has no defs nor uses
        # (otherwise save as block reg)
        for bbname, mbb in bbdict.items():
            mbblen = len(mbb)
            self.block_regs[bbname] = set()
            for reg in self.all_regs:
                if any(self.next_uses[bbname][reg][idx] is not None
                       or self.last_defs[bbname][reg][idx] is not None 
                       for idx in range(-1, mbblen)):
                    self.block_regs[bbname].add(reg)
                else:
                    del self.next_uses[bbname][reg]
                    del self.last_defs[bbname][reg]
            
            self.print_table(bbname)
        
        # Local CFGAnalysis no longer needed
        del self.cfganal
            
    def trace_register(self, start_blocks, reg):
        block_queue = collections.deque(start_blocks)

        # Loop until queue is empty
        while block_queue:
            curr_block = block_queue.popleft()

            mbbaug = self.mbbaugs[curr_block]
            mbblen = len(mbbaug)

            # Check if the next_uses for this block is set, if not initialize with a None in the last line
            if (curr_block, reg, mbblen) not in self.next_uses:
                self.next_uses[(curr_block, reg, mbblen)] = None

            # We assume that the block has been scheduled, if it's either not been processed yet, or its last row changed
            # The list of regs to process this round can be obtained as follows:
            #  * If new_regs is None, process all regs
            #  * Otherwise, process only new_regs

            # We assume that all successors already marked their requires in the last row
            # If not, changes in last row should trigger relaunch of the analysis for the block

            # Process filling next_uses dict
            for idx, (instr, mir_defs, mir_uses) in reversed_enumerate(mbbaug):
                # Copy all next_uses from the next instruction
                self.next_uses[(curr_block, reg, idx)] = self.next_uses[(curr_block, reg, idx+1)]
                
                # For all defs, set next_use to None
                if reg in mir_defs:
                    self.next_uses[(curr_block, reg, idx)] = None

                # Update next_use for mir_uses
                if reg in mir_uses:
                    self.next_uses[(curr_block, reg, idx)] = idx

            # Process the "required" vregs
            # Copy all next_uses from the next instruction
            self.next_uses[(curr_block, reg, -1)] = self.next_uses[(curr_block, reg, 0)]
            
            # Now, do something similar in reverse - note the last defs
            self.last_defs[(curr_block, reg, -1)] = -1 if self.next_uses[(curr_block, reg, -1)] is not None else None

            for idx, (instr, mir_defs, mir_uses) in enumerate(mbbaug):
                # Copy all last_def from the last instruction
                self.last_defs[(curr_block, reg, idx)] = self.last_defs[(curr_block, reg, idx-1)]
            
                # For all uses, update last_def as if use would re-def the register
                if reg in mir_uses:
                    self.last_defs[(curr_block, reg, idx)] = idx
                
                # Update last_def for mir_defs
                if reg in mir_defs:
                    self.last_defs[(curr_block, reg, idx)] = idx

            # Copy all last_defs from the last instruction
            self.last_defs[(curr_block, reg, mbblen)] = self.last_defs[(curr_block, reg, mbblen-1)]
            
            # Finally, if the reg is required (next_use at -1),
            # for each predecessor ensure its used in the last (next_use at their mbblen)
            # and if it was not, (re-)schedule the block
            for pre in self.cfganal.predecessors[curr_block]:
                pre_len = len(self.mbbaugs[pre])
                if self.next_uses[(curr_block, reg, -1)] is not None:
                    if (pre, reg, pre_len) not in self.next_uses or self.next_uses[(pre, reg, pre_len)] is None:
                        self.next_uses[(pre, reg, pre_len)] = pre_len
                        if pre not in block_queue:
                            block_queue.append(pre)
                # Also, if pre was not queried, just schedule it
                else:
                    if (pre, reg, pre_len) not in self.next_uses:
                        block_queue.append(pre)
            
    def print_table(self, bbname):
        print(f">>> Block {bbname}")
        regs = self.block_regs[bbname]
        next_use = self.next_uses[bbname]
        last_def = self.last_defs[bbname]
        mbbaug = self.mbbaugs[bbname]
        mbblen = len(mbbaug)

        fmt_usedef = lambda x: f'{x: 8}' if x is not None else '    None'
        print("\t".join(f'{repr(reg):18}' for reg in regs) + "\n" + "\n".join(
            "\t".join(f"{fmt_usedef(next_use[reg][idx])}, {fmt_usedef(last_def[reg][idx])}" for reg in regs) + (f"\t\t{mbbaug[idx][0]}" if 0 <= idx < mbblen else "")
            for idx in range(-1, mbblen+1))
        )


class Mem2Reg:
    def __init__(self, compilercontext):
        self.compilercontext = compilercontext
    
    def apply(self, bbdict):
        # This analysis requires CFG Analysis
        cfganal = self.compilercontext.get_analysis(CFGAnalysis, False)

        # Register all non-array memory locations (memlocs)
        all_memlocs = {
            op
            for _, mbb in bbdict.items()
            for instr in mbb
            for op in instr.operands
            if isinstance(op, Variable) and not op.isarray
        }

        # For each block, do the following:
        # 1. Record last SSTORE for each variable memory location
        #    (TODO: Array locations?)
        #    and remember the IRValue corresponding to that location
        phi_stores = {}
        for bbname, bb in bbdict.items():
            phi_stores[bbname] = {}

            # We stop on each store and update the dictionary. If it's not the last store,
            # the value will be overriden later.
            for instr in bb:
                if instr.cls is InstrClass.SSTORE:
                    memloc = instr.operands[0]
                    if isinstance(memloc, Variable) and not memloc.isarray:
                        phi_stores[bbname][memloc] = instr.operands[1]
        
        print("PHI Stores:")
        pprint(phi_stores)

        # Pre-2. For each block, if it has 2 or more predecessors, for each memloc in program, prepare a phi node
        pre_imports = {}
        for bbname, bb in bbdict.items():
            pre_imports[bbname] = {}
            if len(cfganal.predecessors[bbname]) > 1:
                phi_list = []
                for memloc in all_memlocs:
                    value = IRValue(InstrClass.PHI, memloc.nextirvar(), (memloc, {pre: None for pre in cfganal.predecessors[bbname]}))
                    phi_list.append(value)
                    pre_imports[bbname][memloc] = value
                # Insert the PHI Nodes at the beginning of the BB
                bb[:0] = phi_list
        
        # Pre-2 cont. For each block, if it has 1 predecessor, for each memloc in program, ask the predecessor for value for the memloc
        def recursive_scan(memloc, bbname):
            # If there is a PHI Store for the memloc in the bb, return the PHI Store
            try:
                return phi_stores[bbname][memloc]
            except KeyError:
                pass
            
            # If there is a pre_import for the memloc, return the pre_import
            try:
                return pre_imports[bbname][memloc]
            except KeyError:
                pass
            
            # If there are no predecessors, return None (undef)
            if not len(cfganal.predecessors[bbname]):
                return None
            
            # Otherwise, there is only one predecessor (for > 1, pre_imports would be non-Null).
            # Scan it recursively.
            pre, = cfganal.predecessors[bbname]
            value = recursive_scan(memloc, pre)
            # Record the value in our pre_imports and return.
            pre_imports[bbname][memloc] = value
            return value
        
        for bbname, bb in bbdict.items():
            if len(cfganal.predecessors[bbname]) == 1:
                for memloc in all_memlocs:
                    if memloc not in pre_imports[bbname]:
                        pre, = cfganal.predecessors[bbname]
                        pre_imports[bbname][memloc] = recursive_scan(memloc, pre)

        print("Pre-imports:")
        pprint(pre_imports)

        # Dynamically check for the last value for the memloc.
        # This is either the phi_store, if present, otherwise pre_import or None.
        def get_post_export(memloc, bbname):
            try:
                return phi_stores[bbname][memloc]
            except KeyError:
                pass
            
            try:        
                return pre_imports[bbname][memloc]
            except KeyError:
                pass
            
            return None
        
        # 2. Perform a PHI-Propagation. For each PHI Node assign incoming values using phi_stores or pre_imports
        for bbname, bb in bbdict.items():
            for instr in bb:
                if instr.cls is InstrClass.PHI:
                    memloc = instr.operands[0]
                    phimap = instr.operands[1]

                    for pre in phimap.keys():
                        export = get_post_export(memloc, pre)
                        print(f"Post-export for {memloc}:{pre} -> {export}")
                        phimap[pre] = export
        
        # 2. cont. Eliminate undef PHIs. Iterate again over all PHI Nodes. Mark those for which all inputs
        # are either None or already marked PHIs. Remove them.
        dead_phis = set()
        changed = True
        while changed:
            changed = False
            for bbname, bb in bbdict.items():
                idx_to_remove = []
                for idx, instr in enumerate(bb):
                    if instr.cls is InstrClass.PHI:
                        if all(val is None 
                               or val in dead_phis  # <- Already-removed PHI
                               or val is instr  # <- Self-referencing
                               for val in instr.operands[1].values()):
                            idx_to_remove.append(idx)
                            dead_phis.add(instr)
                            del pre_imports[bbname][instr.operands[0]]
                for idx in reversed(idx_to_remove):
                    del bb[idx]
                if idx_to_remove:
                    changed = True
        
        # 2. cont. Ensure that dead_phis are not referenced anymore
        for bbname, bb in bbdict.items():
            for idx, instr in enumerate(bb):
                if instr.cls is InstrClass.PHI:
                    phimap = instr.operands[1]

                    for pre, val in phimap.items():
                        if val in dead_phis:
                            phimap[pre] = None

        # 3. Iterate again:
        #    a) For each SSTORE (again for non-array memlocs), record the current variable for this memloc;
        #       Mark the instruction for removal.
        #    b) For each SLOAD (again for non-array memlocs):
        #       *) If it's the first occurrence of this memloc in this block (no SSTORE, no SLOAD), replace
        #          it with a COPY from pre_imports
        #       *) If it's not the first SLOAD, but no SSTORE to this memloc, replace with a COPY from pre_imports
        #       *) If there was a SSTORE, replace with COPY from the SSTORE variable
        for bbname, bb in bbdict.items():
            current_vars = {}

            # The indices must be put in ascending order, as they will be removed in the reverse order
            # (to preserve them while removing).
            idx_to_remove = []

            for idx, instr in enumerate(bb):
                if instr.cls is InstrClass.SSTORE:
                    memloc = instr.operands[0]
                    if isinstance(memloc, Variable) and not memloc.isarray:
                        current_vars[memloc] = instr.operands[1]
                        idx_to_remove.append(idx)
                
                elif instr.cls is InstrClass.SLOAD:
                    memloc = instr.operands[0]
                    if isinstance(memloc, Variable) and not memloc.isarray:
                        if memloc in current_vars:  # Third (*)
                            instr.replace(InstrClass.COPY, (current_vars[memloc],))
                        else:  # First and Second (*)
                            try:
                                instr.replace(InstrClass.COPY, (pre_imports[bbname][memloc],))
                            except KeyError:
                                instr.replace(InstrClass.NOPDEF, ())
            
            for idx in reversed(idx_to_remove):
                del bb[idx]
    
        self.compilercontext.invalidate_analysis(DefUseAnalysis, False)


class DeadValueElimination:
    def __init__(self, compilercontext, is_machine=False):
        self.compilercontext = compilercontext
        self.is_machine = is_machine

        if is_machine:
            self.apply = self.apply_mir
        else:
            self.apply = self.apply_ir

    def apply_ir(self, bbdict):
        # Iterate each BB and each instruction. Note each use and define location for all IRValues.
        # Finally, if an IRValue has use count of 0 and is not on a "critical blacklist" (e.g. GET instr.), remove it
        # from its bb; Repeat process until no change is made
        changed = True
        while changed:
            changed = False

            use_counter = collections.Counter()
            def_helper = {}
            phi_nodes = {}
            for bbname, bb in bbdict.items():
                for idx, instr in enumerate(bb):
                    if instr.cls is InstrClass.PHI:
                        phimap = instr.operands[1]

                        for _, val in phimap.items():
                            if isinstance(val, IRValue):
                                use_counter[val] += 1
                        
                        phi_nodes[instr] = (bbname, idx)
                    else:
                        for op in instr.operands:
                            if isinstance(op, IRValue):
                                use_counter[op] += 1
                    
                    if isinstance(instr, IRValue):
                        def_helper[instr] = (bbname, idx)
        
            to_remove = []
            for var in def_helper:
                if not use_counter[var] and not var.cls.isprotected:
                    to_remove.append(def_helper[var])
            
            if to_remove:
                changed = True

                # Sort to_remove based on reverse of idx, then iterate and remove
                # those instructions.
                to_remove.sort(reverse=True, key=lambda x: x[1])
                for bbname, idx in to_remove:
                    print(f"Removing unused instruction {bbdict[bbname][idx]}")
                    del bbdict[bbname][idx]
                    
                self.compilercontext.invalidate_analysis(DefUseAnalysis, False)

    def apply_mir(self, bbdict):
        # Iterate each block and each instruction. For each non-protected instruction,
        # check if any of its def has "next_use". If no, the instruction is unused.
        defuseanal = self.compilercontext.get_analysis(DefUseAnalysis, True)

        changed = True
        while changed:
            changed = False

            defuseanal.validate(bbdict)

            to_remove = []
            for bbname, mbbaug in defuseanal.mbbaugs.items():
                next_use = defuseanal.next_uses[bbname]

                for idx, (instr, mir_defs, _) in enumerate(mbbaug):
                    if not instr.cls.isprotected:
                        # TODO: currently, DefUseAnalysis only analyzes virtual registers;
                        # if this changes, the following can be adapted.
                        if all(next_use[reg][idx+1] is None for reg in mir_defs) \
                             and not any(isinstance(instr.operands[i], PhysReg) for i in instr.cls.mir_def):
                            to_remove.append((bbname, idx))

            if to_remove:
                changed = True

                # Sort to_remove based on reverse of idx, then iterate and remove
                # those instructions.
                to_remove.sort(reverse=True, key=lambda x: x[1])
                for bbname, idx in to_remove:
                    print(f"Removing unused instruction {bbdict[bbname][idx]}")
                    del bbdict[bbname][idx]
                
                # TODO: find out, how to invalidate partially
                defuseanal.invalidate()


class CopyElision:
    def __init__(self, compilercontext, is_machine=True):
        self.compilercontext = compilercontext

        # If applying on machine code, DefUse analysis can help finding dead copies
        self.defuseanal = self.compilercontext.get_analysis(DefUseAnalysis, is_machine)

        self.is_machine = is_machine

    def apply(self, bbdict):
        """ Elide unnecessary copies.
        For MIR code, this focues on redundant copies within block.
        For IR code, this replaces each use of COPY with its argument.
        """
        if self.is_machine:
            self.changed = True
            while self.changed:
                self.changed = False
                self.global_replace = {}
                self.defuseanal.validate(bbdict)

                for bbname, bb in bbdict.items():
                    self.process_mir_bb(bbname, bb)
        else:
            self.changed = True
            while self.changed: 
                self.changed = False
                self.process_ir_graph(bbdict)
    
    def process_mir_bb(self, bbname, bb):
        # TODO: try to also detect "malicious" copies, i.e. the situation where
        # there are several subsequent copies to the same destination.

        remove_idx = []
        for idx, instr in enumerate(bb):
            if instr.cls is InstrClass.COPY:
                cpsrc = instr.operands[1]
                cpdst = instr.operands[0]
                # Elide self-copies
                if cpsrc == cpdst:
                    remove_idx.append(idx)
                
                # Elide dead copies
                # If the copy dest has no next use in the next instr, it's dead
                # TODO: this can be done for PhysReg as well, if DefUseAnal can support them
                if isinstance(cpdst, VirtReg) and \
                      self.defuseanal.next_uses[bbname][cpdst][idx+1] is None:
                    remove_idx.append(idx)
        
        if remove_idx:
            for idx in reversed(remove_idx):
                del bb[idx]
            
            self.changed = True
    
    def process_ir_graph(self, bbdict):
        # Create a lookup for uses for each IRValue
        defuseanal = self.compilercontext.get_analysis(DefUseAnalysis, False)

        idx_to_remove = []

        def replace_uses(val_of, val_with):
            print(f"Replacing all uses of {val_of} with {val_with}.")
            try:
                for use, opx in defuseanal.use_lookup[val_of]:
                    print(f"-- replacing use in {use}...")
                    if use.cls is InstrClass.PHI:
                        use.operands[1][opx] = val_with
                    else:
                        use.operands = use.operands[:opx] + (val_with,) + use.operands[opx+1:]
            except KeyError:
                print("-- dead instruction")

        for bbname, bb in bbdict.items():
            for idx, instr in enumerate(bb):
                # Find all COPY instructions, add them for deletion and replace all uses
                # with the operand
                if instr.cls is InstrClass.COPY:
                    val = instr.operands[0]
                    replace_uses(instr, val)
                    idx_to_remove.append((bbname, idx))
            
                # Bonus rounds for PHI nodes.
                if instr.cls is InstrClass.PHI:
                    imports = set(instr.operands[1].values())
                    unique_imports = {val for val in imports}
                    other_imports = imports - {instr}

                    # Bonus round, check all phi_nodes for unique values.
                    # If there is only one, unique value, effectively replace PHI with its sole argument
                    if len(unique_imports) == 1:
                        val, *_ = unique_imports
                        print(f"Found a dumb PHI {instr}, replacing all uses with {val}.")
                        replace_uses(instr, val)
                        idx_to_remove.append((bbname, idx))
                    
                    # Bonus round, check all phi_nodes for dumb cycles,
                    # i.e. cases %a = phi(%n, %a)
                    elif len(other_imports) == 1:
                        val, *_ = other_imports
                        print(f"Found a dumb PHI {instr}, replacing all uses with {val}.")
                        replace_uses(instr, val)
                        idx_to_remove.append((bbname, idx))
                    
                    # Bonus round, check all phi_nodes if they have possible undef AND are
                    # for loop variables - these are dead as loop variable is always def.
                    elif instr.operands[0].isloopcounter and None in imports:
                        print(f"Found a dead PHI {instr}, removing and replacing uses with None for propagation.")
                        replace_uses(instr, None)
                        idx_to_remove.append((bbname, idx))
                    
                    # Bonus round, check for all imports in a possible PHI chain,
                    # if there is only one non-PHI import, replace all uses of all the PHIs in chain
                    # with the sole non-PHI value
                    else:
                        chain_imports = set(imports)
                        visited = {instr}
                        last_hash = None
                        next_hash = frozen_hash(visited)
                        while last_hash != next_hash:
                            last_hash = next_hash

                            for imp in (chain_imports - visited):
                                if imp is not None and imp.cls is InstrClass.PHI:
                                    visited.add(imp)
                                    chain_imports.update(imp.operands[1].values())

                            next_hash = frozen_hash(visited)
                        
                        phi_imports = {imp for imp in chain_imports if imp is not None and imp.cls is InstrClass.PHI}
                        non_phi_imports = chain_imports - phi_imports

                        if len(non_phi_imports) == 0:
                            print(f"ERROR: Only PHI chain found: {chain_imports}")
                            exit(-1)
                        elif len(non_phi_imports) == 1:
                            val, *_ = non_phi_imports

                            print(f"Found a dumb PHI chain {phi_imports}, replacing all uses with {val}.")

                            for phi in phi_imports | {instr}:
                                replace_uses(phi, val)
                                idx_to_remove.append(defuseanal.def_lookup[phi])

        if idx_to_remove:
            self.changed = True
            for bbname, bb in bbdict.items():
                for idx in sorted({idx[1] for idx in idx_to_remove if idx[0] == bbname}, reverse=True):
                    del bb[idx]


class ConstPropagation:
    def __init__(self, compilercontext, is_machine):
        self.compilercontext = compilercontext
        self.changed = False
        self.tmpvar = Variable('C')
        self.is_machine = is_machine
    
    # Pre-compute the maximum consecutive INC/DEC stream length, which is better than
    # a CONST + ADD/SUB operation
    max_const_incdec = 1
    while max_const_incdec * InstrClass.INC.cost < (Legalizer.estimate_const_cost(max_const_incdec) + InstrClass.ADD.cost):
        max_const_incdec += 1

    def apply(self, bbdict):
        self.changed = True
        while self.changed:
            self.changed = False

            if self.is_machine:
                for bbname, mbb in bbdict.items():
                    self.process_mir_bb(bbname, mbb)
            else:
                for bbname, bb in bbdict.items():
                    self.process_ir_bb(bbname, bb)

    def process_mir_bb(self, bbname, mbb):
        pass

    def process_ir_bb(self, bbname, bb):
        # For each instruction, if it can benefit from const propagation, check if it applies.
        idx = 0

        while idx < len(bb):
            instr = bb[idx]

            if instr.cls is InstrClass.ADD:
                lhs = instr.operands[0]
                rhs = instr.operands[1]
                # If both ADD operands are const, replace instr with CONST
                if lhs.cls is InstrClass.CONST and rhs.cls is InstrClass.CONST:
                    val = lhs.operands[0] + rhs.operands[0]
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
                # If only one operand is const, either replace it with a sufficient number of INC,
                # or ensure it's the second operand (TODO: check which is better long-term)
                # NOTE: INCs have been moved to ISel to avoid creating tons of copies.
                elif lhs.cls is InstrClass.CONST:
                    # SWAP for canonized operation
                    instr.operands = rhs, lhs
                    changed = True
            elif instr.cls is InstrClass.SUB:
                lhs = instr.operands[0]
                rhs = instr.operands[1]
                # If both SUB operands are const, replace instr with CONST
                if lhs.cls is InstrClass.CONST and rhs.cls is InstrClass.CONST:
                    val = max(0, lhs.operands[0] - rhs.operands[0])
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
                # If only one operand is const, either replace it with a sufficient number of DEC,
                # or ensure it's the second operand (TODO: check which is better long-term)
                # NOTE: DECs have been moved to ISel to avoid creating tons of copies.
            elif instr.cls is InstrClass.MUL:
                lhs = instr.operands[0]
                rhs = instr.operands[1]
                # If both MUL operands are const, replace instr with CONST
                if lhs.cls is InstrClass.CONST and rhs.cls is InstrClass.CONST:
                    val = lhs.operands[0] * rhs.operands[0]
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
                # If only one operand is const, unroll the MUL loop
                elif lhs.cls is InstrClass.CONST or rhs.cls is InstrClass.CONST:
                    # swap for a common routine:
                    if lhs.cls is InstrClass.CONST:
                        rhs, lhs = lhs, rhs
                    
                    val = rhs.operands[0]
                    if val == 0:
                        print(f"Const evaluation: {instr} -> {val}")
                        instr.replace(InstrClass.CONST, (val,))
                    elif val == 1:
                        print(f"Const evaluation: {instr} -> {lhs}")
                        instr.replace(InstrClass.COPY, (lhs,))
                    else:
                        rep = bin(val)[3::]
                        # We know the MSB was 1
                        new_instrs = []
                        next_val = lhs
                        for b in rep:
                            next_var = self.tmpvar.nextirvar()
                            next_val = IRValue(InstrClass.ADD, next_var, (next_val, next_val))
                            new_instrs.append(next_val)
                            if b == '1':
                                next_var = self.tmpvar.nextirvar()
                                next_val = IRValue(InstrClass.ADD, next_var, (next_val, lhs))
                                new_instrs.append(next_val)
                        # Patch the last instr
                        print(f"Const expansion: {instr} -> {new_instrs}")
                        *new_instrs, last = new_instrs
                        instr.replace(last.cls, last.operands)

                        bb[idx:idx] = new_instrs
                        idx += len(new_instrs)

                    changed = True
            elif instr.cls is InstrClass.DIV:
                lhs = instr.operands[0]
                rhs = instr.operands[1]
                # If both DIV operands are const, replace instr with CONST
                if lhs.cls is InstrClass.CONST and rhs.cls is InstrClass.CONST:
                    if rhs.operands[0] == 0:
                        val = 0
                    else:
                        val = lhs.operands[0] // rhs.operands[0]
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
            elif instr.cls is InstrClass.REM:
                lhs = instr.operands[0]
                rhs = instr.operands[1]
                # If both REM operands are const, replace instr with CONST
                if lhs.cls is InstrClass.CONST and rhs.cls is InstrClass.CONST:
                    if rhs.operands[0] == 0:
                        val = 0
                    else:
                        val = lhs.operands[0] % rhs.operands[0]
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
            elif instr.cls is InstrClass.INC:
                val = instr.operands[0]
                if val.cls is InstrClass.CONST:
                    val = val.operands[0] + 1
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
            elif instr.cls is InstrClass.DEC:
                val = instr.operands[0]
                if val.cls is InstrClass.CONST:
                    val = max(0, val.operands[0] - 1)
                    print(f"Const evaluation: {instr} -> {val}")
                    instr.replace(InstrClass.CONST, (val,))
                    changed = True
            elif instr.cls is InstrClass.SJZERO:
                val = instr.operands[0]
                if val.cls is InstrClass.CONST:
                    if val.operands[0] > 0:
                        print(f"Const jump selection: {instr} -> JUMP {instr.operands[2]}")
                        instr.replace(InstrClass.JUMP, (instr.operands[2],))
                    else:
                        print(f"Const jump selection: {instr} -> JUMP {instr.operands[1]}")
                        instr.replace(InstrClass.JUMP, (instr.operands[1],))
                    changed = True
            elif instr.cls is InstrClass.SJODD:
                val = instr.operands[0]
                if val.cls is InstrClass.CONST:
                    if val.operands[0] & 1 == 0:
                        print(f"Const jump selection: {instr} -> JUMP {instr.operands[2]}")
                        instr.replace(InstrClass.JUMP, (instr.operands[2],))
                    else:
                        print(f"Const jump selection: {instr} -> JUMP {instr.operands[1]}")
                        instr.replace(InstrClass.JUMP, (instr.operands[1],))
                    changed = True

            idx += 1


class Rewriter:
    MIRRule = collections.namedtuple('MIRRule', ('pattern', 'replace', 'usereq'))

    IRRule = collections.namedtuple('IRRule', ('trigger', 'chain', 'replace', 'usereq'))

    class MatchFailure(Exception):
        pass

    # Flags for 'usereq' rules
    RegUsed = 0
    RegUnused = 1

    def __init__(self, compilercontext, is_machine):
        self.compilercontext = compilercontext
        self.is_machine = is_machine

    def apply(self, bbdict):
        if self.is_machine:
            for bbname, mbb in bbdict.items():
                self.process_mir_bb(bbname, mbb)
        else:
            for bbname, bb in bbdict.items():
                self.process_ir_bb(bbname, bb)

    mir_rules = [
        # Redundant COPY before STORE (the other COPY should be elided if dead)
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.SSTORE, 'Z', 'Y')),
                ((InstrClass.SSTORE, 'Z', 'X'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.SSTORE, 'Z', 'Y')),
                ((InstrClass.SSTORE, 'Z', 'X'), (InstrClass.COPY, 'Y', 'X')),
                ()
               ),
        # Redundant COPY around INC/DEC (same reg)
        # The first 2 rules are for a dead Y, the other 2 are for the other cases
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.INC, 'Y'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.INC, 'X'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.DEC, 'Y'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.DEC, 'X'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.INC, 'Y'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.INC, 'X'), (InstrClass.COPY, 'Y', 'X')),
                ()
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.DEC, 'Y'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.DEC, 'X'), (InstrClass.COPY, 'Y', 'X')),
                ()
               ),
        # Redundant COPY around INC/DEC/HALF (diff reg)
        # NOTE: This only works if Y is a vreg
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.INC, 'Y'), (InstrClass.COPY, 'Z', 'Y')),
                ((InstrClass.COPY, 'Z', 'X'), (InstrClass.INC, 'Z'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.DEC, 'Y'), (InstrClass.COPY, 'Z', 'Y')),
                ((InstrClass.COPY, 'Z', 'X'), (InstrClass.DEC, 'Z'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.HALF, 'Y'), (InstrClass.COPY, 'Z', 'Y')),
                ((InstrClass.COPY, 'Z', 'X'), (InstrClass.HALF, 'Z'),),
                ((RegUnused, 'Y'),)
               ),
        # Redundant COPY around ADD/SUB (same reg)
        # The first 2 rules are for a dead Y, the other 2 are for the other cases
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.ADD, 'Y', 'Z'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.ADD, 'X', 'Z'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.SUB, 'Y', 'Z'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.ADD, 'X', 'Z'),),
                ((RegUnused, 'Y'),)
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.ADD, 'Y', 'Z'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.ADD, 'X', 'Z'), (InstrClass.COPY, 'Y', 'X')),
                ()
               ),
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.SUB, 'Y', 'Z'), (InstrClass.COPY, 'X', 'Y')),
                ((InstrClass.ADD, 'X', 'Z'), (InstrClass.COPY, 'Y', 'X')),
                ()
               ),
        # Redundant COPY before COPY (unused COPY should be elided if dead)
        MIRRule(((InstrClass.COPY, 'Y', 'X'), (InstrClass.COPY, 'Z', 'Y')),
                ((InstrClass.COPY, 'Z', 'X'),),
                ((RegUnused, 'Y'),)
               ),
        # Redundant LEA and reload
        MIRRule(((InstrClass.LEA, '@X', '$T', 'I'), (InstrClass.SSTORE, '@X', 'A'), (InstrClass.LEA, '@Y', '$T', 'I'), (InstrClass.SLOAD, 'B', '@Y')),
                ((InstrClass.LEA, '@X', '$T', 'I'), (InstrClass.SSTORE, '@X', 'A'), (InstrClass.COPY, 'B', 'A')),
                ()
               ),
    ]

    ir_rules = [
        # a := b % 2
        # IF a = 1 ...
        # This part rewrites the always-true jump; this should also work for other cases,
        # e.g. for a<1, a>1, and so on
        IRRule((InstrClass.SJZERO, '%A', '#L0', '#L1'),
               (('%A', InstrClass.SUB, '%C', '%1'),
                ('%C', InstrClass.REM, '%B', '%2'),
                ('%2', InstrClass.CONST, 2),
                ('%1', InstrClass.CONST, 1),),
               (InstrClass.JUMP, '#L0'),
               ()
              ),
        # This part rewrites the "if odd" jump
        IRRule((InstrClass.SJZERO, '%A', '#L0', '#L1'),
               (('%A', InstrClass.SUB, '%1', '%C'),
                ('%C', InstrClass.REM, '%B', '%2'),
                ('%2', InstrClass.CONST, 2),
                ('%1', InstrClass.CONST, 1),),
               (InstrClass.SJODD, '%B', '#L0', '#L1'),
               ()
              ),
    ]

    def process_mir_bb(self, bbname, mbb):
        defuseanal = self.compilercontext.get_analysis(DefUseAnalysis, True)

        # TODO: write a parser?
        for rule in self.mir_rules:
            pattern_len = len(rule.pattern)
            idx = 0
            while idx + pattern_len <= len(mbb):
                try:
                    # First, check if instruction classes match
                    if all(mbb[idx+i].cls is rule.pattern[i][0] for i in range(pattern_len)):
                        # Then, try to match variables
                        matched = {}
                        for i in range(pattern_len):
                            for j, v in enumerate(rule.pattern[i][1:]):
                                #print(f"bbname: {bbname}; idx: {idx}; rule: {rule}; i: {i}; matched = {matched}")
                                op = mbb[idx+i].operands[j]
                                if v in matched:
                                    if matched[v] != op:
                                        raise self.MatchFailure()
                                elif v[0] == '@' and not isinstance(op, VirtReg):
                                    raise self.MatchFailure()
                                elif v[0] == '!' and not isinstance(op, PhysReg):
                                    raise self.MatchFailure()
                                elif v[0] == '$' and not isinstance(op, Variable):
                                    raise self.MatchFailure()
                                matched[v] = op

                        # Check used/unused requirements
                        for ur in rule.usereq:
                            req, reg = ur
                            vreg = matched[reg]
                            # TODO: DefUseAnalysis only analyze vregs; fix if it changes
                            if not isinstance(vreg, VirtReg):
                                raise self.MatchFailure()
                            next_use = defuseanal.next_uses[bbname][vreg][idx + pattern_len]
                            if req is self.RegUnused and next_use is not None:
                                raise self.MatchFailure()
                            if req is self.RegUsed and next_use is None:
                                raise self.MatchFailure()

                        repl = [
                            MIRInstr(r[0], tuple(matched[v] for v in r[1:]))
                            for r in rule.replace
                        ]
                        # If all matched, replace:
                        print("Rewriting:")
                        pprint(mbb[idx:idx+pattern_len])
                        print("with:")
                        pprint(repl)

                        mbb[idx:idx+pattern_len] = repl

                        # Re-request analysis since mbb has changed
                        # TODO: actually, we only need to request update for this particular bb
                        defuseanal.invalidate()
                        defuseanal.validate(self.compilercontext.mbbs)
                except self.MatchFailure:
                    pass

                idx += 1

        self.compilercontext.invalidate_analysis(CFGAnalysis, False)

    def process_ir_bb(self, bbname, bb):
        # TODO: write a parser?
        for rule in self.ir_rules:
            idx = 0
            while idx < len(bb):
                # Iterate, until a trigger class matches the instruction class
                instr = bb[idx]
                try:
                    if instr.cls is rule.trigger[0]:
                        # Then, try to match variables
                        matched = {}
                        # NOTE: explicit assumption that instr and rule trigger have equal
                        # number of operands.
                        for op, v in zip(instr.operands, rule.trigger[1:]):
                            if v in matched:
                                if matched[v] != op:
                                    raise self.MatchFailure()
                            elif v[0] == '%' and not isinstance(op, IRValue):
                                raise self.MatchFailure()
                            elif v[0] == '#' and not isinstance(op, str):
                                raise self.MatchFailure()
                            else:
                                matched[v] = op

                        for c in rule.chain:
                            cv = c[0]
                            cval = matched[cv]
                            # For a value in chain, check if the class matches
                            # and then if operands match
                            if cval.cls is not c[1]:
                                raise self.MatchFailure()
                            for op, v in zip(cval.operands, c[2:]):
                                if not isinstance(v, str):
                                    if op != v:
                                        raise self.MatchFailure()
                                elif v in matched:
                                    if matched[v] != op:
                                        raise self.MatchFailure()
                                elif v[0] == '%' and not isinstance(op, IRValue):
                                    raise self.MatchFailure()
                                elif v[0] == '#' and not isinstance(op, str):
                                    raise self.MatchFailure()
                                else:
                                    matched[v] = op

                        print("Rewriting:")
                        print(bb[idx])
                        bb[idx].replace(rule.replace[0], tuple(matched[v] for v in rule.replace[1:]))
                        print("with:")
                        print(bb[idx])

                except self.MatchFailure:
                    pass
                idx += 1

        self.compilercontext.invalidate_analysis(CFGAnalysis, False)


class CompilerContext:
    def __init__(self):
        self.varmap = {}
        self.loopvars = {}
        self.bbs = {}
        self.mbbs = None  # bbs are converted to mbbs at instruction selection (isel)
        self.bbnamecount = collections.Counter()

        self.analyses = {}

    def declare_var(self, varname):
        self.varmap[varname] = Variable.get(varname)

    def declare_array(self, varname, start, stop):
        self.varmap[varname] = ArrayVariable.get(varname, start, stop)

    def createbb(self, bbnamepref=''):
        idx = self.bbnamecount[bbnamepref]
        name = f"{bbnamepref}_{idx}"
        self.bbs[name] = []
        self.bbnamecount[bbnamepref] += 1
        return name

    def creatembb(self, bbnamepref=''):
        idx = self.bbnamecount[bbnamepref]
        name = f"{bbnamepref}_{idx}"
        self.mbbs[name] = []
        self.bbnamecount[bbnamepref] += 1
        return name

    def get_analysis(self, analcls, is_machine=False):
        # Analysis caching: if the analysis has already been performed/instantiated,
        # return the instance, otherwise create a new one
        try:
            analysis = self.analyses[(is_machine, id(analcls))]
            # Ensure the analysis is valid before returning it
            analysis.validate(self.mbbs if is_machine else self.bbs)

        except KeyError:
            analysis = analcls(self, is_machine)
            self.analyses[(is_machine, id(analcls))] = analysis
            # A fresh analysis is always invalid, so perform full analysis directly
            analysis.analyze(self.mbbs if is_machine else self.bbs)

        assert analysis is not None
        return analysis

    def invalidate_analysis(self, analcls, is_machine=False):
        # Check if analysis in cache; if so, invalidate it
        try:
            self.analyses[(is_machine, id(analcls))].invalidate()
        except KeyError:
            pass

    def parse_ast(self, commands):
        # Iterate over the commands, generate and fill the basic blocks
        # (First IR translation from AST to IR)

        irbuilder = IRBuilder(self)
        irbuilder.beginbb()

        def emit_value_load(value):
            if value[0] == 'NUM':
                val = int(value[1])
                val_irval = irbuilder.tmpvar.nextirvar()
                val_instr = irbuilder.add_var(val_irval, InstrClass.CONST, val)
            elif value[0] == 'VAR':
                var = self.varmap[value[1]]
                val_instr = var.emit_load(irbuilder)
            elif value[0] == 'ARRI':
                arr = self.varmap[value[1]]
                idx = int(value[2])
                idx_irvar = irbuilder.tmpvar.nextirvar()
                idx_instr = irbuilder.add_var(idx_irvar, InstrClass.CONST, idx)
                val_instr = arr.emit_load(irbuilder, idx_instr)
            elif value[0] == 'ARRX':
                arr = self.varmap[value[1]]
                idx = self.varmap[value[2]]
                idx_instr = idx.emit_load(irbuilder)
                val_instr = arr.emit_load(irbuilder, idx_instr)
            else:
                raise ValueError("Invalid value '{}'".format(value))
            return val_instr

        def emit_identifier_store(ident, instr):
            if ident[0] == 'VAR':
                var = self.varmap[ident[1]]
                var.emit_store(irbuilder, instr)
            elif ident[0] == 'ARRI':
                arr = self.varmap[ident[1]]
                idx = int(ident[2])
                idx_irvar = irbuilder.tmpvar.nextirvar()
                idx_instr = irbuilder.add_var(idx_irvar, InstrClass.CONST, idx)
                arr.emit_store(irbuilder, idx_instr, instr)
            elif ident[0] == 'ARRX':
                arr = self.varmap[ident[1]]
                idx = self.varmap[ident[2]]
                idx_instr = idx.emit_load(irbuilder)
                arr.emit_store(irbuilder, idx_instr, instr)

        def emit_cond_block(cond, bbiftrue, bbiffalse):
            if cond[0] == 'EQ':
                op0_instr = emit_value_load(cond[1])
                op1_instr = emit_value_load(cond[2])
                # EQ (a, b):
                # GT (a, b) -> false, cont
                #cont:
                # GT (b, a) -> false, true
                # Create an additional cont bb
                eq_cont_bb = self.createbb('eq_cont')

                cmp_irvar = irbuilder.tmpvar.nextirvar()
                cmp_irval = irbuilder.add_var(cmp_irvar, InstrClass.SUB, op0_instr, op1_instr)
                irbuilder.add_instr(InstrClass.SJZERO, cmp_irval, eq_cont_bb, bbiffalse)

                irbuilder.switchbb(eq_cont_bb)
                cmp_irvar = irbuilder.tmpvar.nextirvar()
                cmp_instr = irbuilder.add_var(cmp_irvar, InstrClass.SUB, op1_instr, op0_instr)
                irbuilder.add_instr(InstrClass.SJZERO, cmp_instr, bbiftrue, bbiffalse)
            elif cond[0] == 'NEQ':
                emit_cond_block(('EQ', cond[1], cond[2]), bbiffalse, bbiftrue)
            elif cond[0] == 'GT':
                op0_instr = emit_value_load(cond[1])
                op1_instr = emit_value_load(cond[2])
                cmp_irvar = irbuilder.tmpvar.nextirvar()
                cmp_instr = irbuilder.add_var(cmp_irvar, InstrClass.SUB, op0_instr, op1_instr)
                irbuilder.add_instr(InstrClass.SJZERO, cmp_instr, bbiffalse, bbiftrue)
            elif cond[0] == 'LT':
                emit_cond_block(('GT', cond[2], cond[1]), bbiftrue, bbiffalse)
            elif cond[0] == 'GEQ':
                emit_cond_block(('GT', cond[2], cond[1]), bbiffalse, bbiftrue)
            elif cond[0] == 'LEQ':
                emit_cond_block(('GT', cond[1], cond[2]), bbiffalse, bbiftrue)

        def reentrant_parse(lst):
            for cmd in lst:
                if cmd[0] == 'READ':
                    get_irvar = irbuilder.tmpvar.nextirvar()
                    get_instr = irbuilder.add_var(get_irvar, InstrClass.GET)
                    emit_identifier_store(cmd[1], get_instr)

                elif cmd[0] == 'WRITE':
                    val_instr = emit_value_load(cmd[1])
                    irbuilder.add_instr(InstrClass.PUT, val_instr)

                elif cmd[0] == 'ASSIGN':
                    # Generate load/compute to ass_instr first

                    if cmd[2][0] == 'VALUE':
                        ass_instr = emit_value_load(cmd[2][1])
                    else:
                        op0_instr = emit_value_load(cmd[2][1])
                        op1_instr = emit_value_load(cmd[2][2])
                        ass_irvar = irbuilder.tmpvar.nextirvar()

                        if cmd[2][0] == 'ADD':
                            ass_instr = irbuilder.add_var(ass_irvar, InstrClass.ADD, op0_instr, op1_instr)
                        elif cmd[2][0] == 'SUB':
                            ass_instr = irbuilder.add_var(ass_irvar, InstrClass.SUB, op0_instr, op1_instr)
                        elif cmd[2][0] == 'MUL':
                            ass_instr = irbuilder.add_var(ass_irvar, InstrClass.MUL, op0_instr, op1_instr)
                        elif cmd[2][0] == 'DIV':
                            ass_instr = irbuilder.add_var(ass_irvar, InstrClass.DIV, op0_instr, op1_instr)
                        elif cmd[2][0] == 'REM':
                            ass_instr = irbuilder.add_var(ass_irvar, InstrClass.REM, op0_instr, op1_instr)
                        else:
                            raise ValueError("Invalid expression: '{}'".format(cmd[2]))

                    emit_identifier_store(cmd[1], ass_instr)

                elif cmd[0] == 'WHILE':
                    # Create a couple of basic blocks: loop header, body, and cont
                    loop_head_bb = self.createbb('loop_head')
                    loop_body_bb = self.createbb('loop_body')
                    curr_cont_bb = self.createbb(irbuilder.currentbbname)
                    # Add unconditional jump to the loop_head_bb
                    irbuilder.add_instr(InstrClass.JUMP, loop_head_bb)
                    # Switch to the header block
                    irbuilder.switchbb(loop_head_bb)
                    # Emit cond code
                    emit_cond_block(cmd[1], loop_body_bb, curr_cont_bb)
                    # Switch to body block and emit it recursively
                    irbuilder.switchbb(loop_body_bb)
                    reentrant_parse(cmd[2])
                    # Emit jump back to header and switch to cont
                    irbuilder.add_instr(InstrClass.JUMP, loop_head_bb)
                    irbuilder.switchbb(curr_cont_bb)

                elif cmd[0] == 'DO':
                    # Create a couple of basic blocks: loop tail, body, and cont
                    loop_tail_bb = self.createbb('loop_tail')
                    loop_body_bb = self.createbb('loop_body')
                    curr_cont_bb = self.createbb(irbuilder.currentbbname)
                    # Add unconditional jump to the loop_body_bb
                    irbuilder.add_instr(InstrClass.JUMP, loop_body_bb)
                    # Switch to body block and emit it recursively
                    irbuilder.switchbb(loop_body_bb)
                    reentrant_parse(cmd[2])
                    # Emit jump to tail
                    irbuilder.add_instr(InstrClass.JUMP, loop_tail_bb)
                    # Switch to the tail block
                    irbuilder.switchbb(loop_tail_bb)
                    # Emit cond code and switch to cont
                    emit_cond_block(cmd[1], loop_body_bb, curr_cont_bb)
                    irbuilder.switchbb(curr_cont_bb)

                elif cmd[0] == 'FOR':
                    # Define a loop variable
                    varname = cmd[2]

                    loopvarname = varname
                    loopvar = Variable.get(varname, isloopcounter=True)
                    self.varmap[loopvarname] = loopvar

                    loopctrname = varname + '$loopcount'
                    loopctr = Variable.get(loopctrname, isloopcounter=True)
                    self.varmap[loopctrname] = loopctr

                    # Create a couple of basic blocks: loop header, body, and cont
                    loop_body_bb = self.createbb('loop_body')
                    curr_cont_bb = self.createbb(irbuilder.currentbbname)

                    # Load the initial value to the loop counter
                    from_instr = emit_value_load(cmd[3])
                    irbuilder.add_instr(InstrClass.SSTORE, loopvar, from_instr)
                    # Compute the total number of iterations
                    # as B + 1 - A (for .. to .. loop)
                    # or A + 1 - B (for .. downto .. loop)
                    to_instr = emit_value_load(cmd[4])
                    if cmd[1] == 1:  # for .. to .. loop
                        tmp_irvar = irbuilder.tmpvar.nextirvar()
                        tmp_instr = irbuilder.add_var(tmp_irvar, InstrClass.INC, to_instr)

                        ctr_irvar = loopctr.nextirvar()
                        ctr_instr = irbuilder.add_var(ctr_irvar, InstrClass.SUB, tmp_instr, from_instr)
                    else:  # for .. downto .. loop
                        tmp_irvar = irbuilder.tmpvar.nextirvar()
                        tmp_instr = irbuilder.add_var(tmp_irvar, InstrClass.INC, from_instr)

                        ctr_irvar = loopctr.nextirvar()
                        ctr_instr = irbuilder.add_var(ctr_irvar, InstrClass.SUB, tmp_instr, to_instr)

                    irbuilder.add_instr(InstrClass.SSTORE, loopctr, ctr_instr)
                    irbuilder.add_instr(InstrClass.SJZERO, ctr_instr, curr_cont_bb, loop_body_bb)

                    # Switch to body block and emit it recursively
                    irbuilder.switchbb(loop_body_bb)
                    reentrant_parse(cmd[5])

                    # At the end of the body:
                    # * load loop counter, decrement it and check if it's 0
                    # * load loop variable, increment/decrement it and store it back
                    tmp_irvar = irbuilder.tmpvar.nextirvar()
                    tmp_instr = irbuilder.add_var(tmp_irvar, InstrClass.SLOAD, loopvar)
                    var_irvar = irbuilder.tmpvar.nextirvar()
                    if cmd[1] == 1:  # for .. to .. loop
                        var_instr = irbuilder.add_var(var_irvar, InstrClass.INC, tmp_instr)
                    else:  # for .. downto .. loop
                        var_instr = irbuilder.add_var(var_irvar, InstrClass.DEC, tmp_instr)
                    irbuilder.add_instr(InstrClass.SSTORE, loopvar, var_instr)

                    tmp_irvar = irbuilder.tmpvar.nextirvar()
                    tmp_instr = irbuilder.add_var(tmp_irvar, InstrClass.SLOAD, loopctr)
                    ctr_irvar = irbuilder.tmpvar.nextirvar()
                    ctr_instr = irbuilder.add_var(ctr_irvar, InstrClass.DEC, tmp_instr)
                    irbuilder.add_instr(InstrClass.SSTORE, loopctr, ctr_instr)

                    irbuilder.add_instr(InstrClass.SJZERO, ctr_instr, curr_cont_bb, loop_body_bb)

                    # Switch to cont
                    irbuilder.switchbb(curr_cont_bb)

                    # Remove the loop variables from lookup tables
                    del self.varmap[loopvarname]
                    del self.varmap[loopctrname]

                    # Save the loop variables in a special map for mem alloc
                    try:
                        self.loopvars[loopvarname].append(loopvar)
                    except KeyError:
                        self.loopvars[loopvarname] = [loopvar]
                    try:
                        self.loopvars[loopctrname].append(loopctr)
                    except KeyError:
                        self.loopvars[loopctrname] = [loopctr]

                elif cmd[0] == 'IF':
                    # Create a couple of basic blocks: if true, if false, and cont
                    if_then_bb = self.createbb('if_then')
                    if_else_bb = self.createbb('if_else')
                    curr_cont_bb = self.createbb(irbuilder.currentbbname)
                    # Emit cond code
                    emit_cond_block(cmd[1], if_then_bb, if_else_bb)

                    # Switch to if true block and emit it recursively
                    irbuilder.switchbb(if_then_bb)
                    reentrant_parse(cmd[2])
                    # Emit jump to cont
                    irbuilder.add_instr(InstrClass.JUMP, curr_cont_bb)

                    # Switch to if false block and emit it recursively
                    irbuilder.switchbb(if_else_bb)
                    reentrant_parse(cmd[3])
                    # Emit jump to cont
                    irbuilder.add_instr(InstrClass.JUMP, curr_cont_bb)

                    # Switch to the cont block
                    irbuilder.switchbb(curr_cont_bb)

                else:
                    print("Unknown AST node:", cmd[0], "- Skipping...")

        reentrant_parse(commands)
        # Add HALT command at the end of the last active block (as if there was one more cmd)
        irbuilder.add_instr(InstrClass.HALT)

    def run_isel(self):
        isel = ISel(self)
        self.mbbs = {}

        for bbname, bb in self.bbs.items():
            mbb = isel.process_block(bb)
            self.mbbs[bbname] = mbb

        for bbname, mbb in self.mbbs.items():
            isel.phi_elimination(mbb)

    def run_legalize(self):
        legalizer = Legalizer(self)

        for bbname, mbb in self.mbbs.items():
            mbb = legalizer.legalize_lea(mbb)
            mbb = legalizer.legalize_sload(mbb)
            mbb = legalizer.legalize_sstore(mbb)
            mbb = legalizer.legalize_const(mbb)
            self.mbbs[bbname] = mbb

        legalizer.legalize_muldiv()

        for bbname, mbb in self.mbbs.items():
            mbb = legalizer.legalize_sjumps(mbb)
            mbb = legalizer.legalize_noops(mbb)
            self.mbbs[bbname] = mbb

        self.invalidate_analysis(CFGAnalysis, True)
        self.invalidate_analysis(DefUseAnalysis, True)

    def run_malloc(self):
        memidx = 0

        # Count number of memory access for each variable
        memcount = collections.Counter()
        for _, mbb in self.mbbs.items():
            for instr in mbb:
                for op in instr.operands:
                    if isinstance(op, Variable):
                        memcount[op] += 1

        # Print stats
        print(">>> Memcount:")
        print(memcount)

        for var, _ in memcount.most_common():
            var.memidx = memidx
            if isinstance(var, ArrayVariable):
                memidx += var.length
            else:
                memidx += 1

    def run_regalloc(self):
        regalloc = RegAlloc(self)
        regalloc.process()

    def run_codegen(self, stream):
        codegen = CodeGen(self)
        codegen.gen_to_stream(stream, 'init')

    def run_iropt(self):
        # TODO: Establish pipeline/compress the many functions?
        mem2reg = Mem2Reg(self)
        copyelision = CopyElision(self, False)
        constpropagation = ConstPropagation(self, False)
        rewriter = Rewriter(self, False)
        dve = DeadValueElimination(self, False)

        mem2reg.apply(self.bbs)
        print(">> IROpt After Mem2Reg")
        self.dump_ir()

        copyelision.apply(self.bbs)
        print(">> IROpt After CopyElision")
        self.dump_ir()

        constpropagation.apply(self.bbs)
        print(">> IROpt After ConstPropagation")
        self.dump_ir()

        rewriter.apply(self.bbs)
        print(">> IROpt After Rewriter")
        self.dump_ir()

        copyelision.apply(self.bbs)
        print(">> IROpt After CopyElision")
        self.dump_ir()

        dve.apply(self.bbs)
        print(">> IROpt After DeadValueElimination")
        self.dump_ir()

        copyelision.apply(self.bbs)
        print(">> IROpt After CopyElision")
        self.dump_ir()

    def run_miropt(self):
        # TODO: Establish pipeline/compress the many functions?
        copyelision = CopyElision(self, True)
        rewriter = Rewriter(self, True)
        dve = DeadValueElimination(self, True)

        copyelision.apply(self.mbbs)
        print(">> MIROpt After CopyElision")
        self.dump_mir()

        dve.apply(self.mbbs)
        print(">> MIROpt After DeadValueElimination")
        self.dump_mir()

        copyelision.apply(self.mbbs)
        print(">> MIROpt After CopyElision")
        self.dump_mir()

        rewriter.apply(self.mbbs)
        print(">> MIROpt After Rewriter")
        self.dump_mir()

        copyelision.apply(self.mbbs)
        print(">> MIROpt After CopyElision")
        self.dump_mir()

        dve.apply(self.mbbs)
        print(">> MIROpt After DeadValueElimination")
        self.dump_mir()

        copyelision.apply(self.mbbs)
        print(">> MIROpt After CopyElision")
        self.dump_mir()

    def dump_ir(self):
        for bbname, bb in self.bbs.items():
            print("#{}:".format(bbname))

            for instr in bb:
                print("  {}".format(instr))

    def dump_mir(self):
        for bbname, bb in self.mbbs.items():
            print("#{}:".format(bbname))

            for instr in bb:
                print("  {}".format(instr))


class CodeGen:
    def __init__(self, compilercontext: CompilerContext):
        self.compilercontext = compilercontext

    def gen_to_stream(self, stream, init_block='init'):
        # 1. Glue blocks to a single list, remember all labels
        labels = dict()
        labels_inv = dict()
        pending_blocks = set(self.compilercontext.mbbs.keys())
        final_stream = []

        # Quick analysis: for each block check if it ends with a jump to another block and note that block
        fallthrough_blocks = dict()
        for bbname in pending_blocks:
            terminator = self.compilercontext.mbbs[bbname][-1]
            if terminator.cls == InstrClass.JUMP and terminator.operands[0] != bbname:
                fallthrough_blocks[bbname] = terminator.operands[0]

        # Quick analysis: same as before, but remember all possibly incoming blocks
        parent_blocks = dict()
        for bbname in fallthrough_blocks:
            child = fallthrough_blocks[bbname]
            try:
                parent_blocks[child].append(bbname)
            except KeyError:
                parent_blocks[child] = [bbname]

        # Quick analysis: for each block, find the longest fallthrough chain starting with it and note if it's a cycle
        fallthrough_chains = dict()
        for bbname in pending_blocks:
            if bbname not in fallthrough_blocks:
                fallthrough_chains[bbname] = (0, False)
            else:
                # Naive implementation - this could be done much better, I know
                tmp = {bbname}
                node = bbname
                cycle = False
                while node in fallthrough_blocks and not cycle:
                    node = fallthrough_blocks[node]
                    # Failsafe for cycle detection
                    t1 = len(tmp)
                    tmp.add(node)
                    t2 = len(tmp)
                    if t1 == t2:
                        cycle = True

                fallthrough_chains[bbname] = (len(tmp) - 1, cycle)

        # Start stiching the blocks together
        current_block = init_block

        while True:
            pending_blocks.remove(current_block)
            idx = len(final_stream)
            # Store the index of the current block
            labels[current_block] = idx
            # Update also the inverse labels
            try:
                labels_inv[idx].append(current_block)
            except KeyError:
                labels_inv[idx] = [current_block]
            # Copy instructions from the current mbb to the final_stream list, until
            # a JUMP or HALT (the only valid terminators at this point)
            mbb = self.compilercontext.mbbs[current_block]
            final_stream += mbb[:-1]
            terminator = mbb[-1]
            # Depending on the last instruction:
            # a) If it's a JUMP and its target block is in pending_blocks, set it as current_block and skip the jump
            if terminator.cls == InstrClass.JUMP and terminator.operands[0] in pending_blocks:
                current_block = terminator.operands[0]
            # b) If it's a JUMP but its target block is not in pending_blocks; or
            # c) If it's a HALT, then push the terminator to the final_stream and try to find a new current_block
            else:
                final_stream.append(terminator)

                # Check if there are actually any blocks left, exit if not
                if not pending_blocks:
                    break

                # Otherwise, from fallthrough_chains, find the longest chain
                # TODO: research which node to chose in case of cycles

                tmp = [(bbname, length) for bbname, (length, _) in fallthrough_chains.items() if bbname in pending_blocks]
                tmp.sort(key=lambda x: x[1], reverse=True)
                current_block = tmp[0][0]

        # 2. Iterate over the glued list. When at label index, emit label comment before writing command.
        for i, instr in enumerate(final_stream):
            if i in labels_inv:
                for lbl in labels_inv[i]:
                    stream.write('# {} \n'.format(lbl))
            # Format operands: PhysReg pass as name letters, strs replace with label indices, leave the rest for debug
            ops = [
                str(labels[op]) if isinstance(op, str) else
                op.name if isinstance(op, PhysReg) else
                repr(op)
                for op in instr.operands
            ]
            stream.write('{:6} {:15}  # {:03} {}\n'.format(instr.cls.name, ' '.join(ops), i, instr))


class Lexer(sly.Lexer):
    tokens = { DECLARE, IN, END,
               ASSIGN,
               IF, THEN, ELSE, ENDIF,
               WHILE, DO, ENDWHILE, ENDDO,
               FOR, FROM, TO, DOWNTO, DO, ENDFOR,
               READ, WRITE,
               PLUS, MINUS, ASTERISK, FSLASH, PERCENT,
               EQ, NEQ, LT, GT, LEQ, GEQ,
               LPAREN, RPAREN, SEMICOLON, COLON,
               PIDENTIFIER, NUM,
             }

    ignore_whitespace = r'\s'
    ignore_comment = r'[\[][^\]]*[\]]'

    # Ordered alphabetically as apparently it's match-first, not match-longest
    DECLARE    = r'DECLARE'
    DOWNTO     = r'DOWNTO'
    DO         = r'DO'
    ELSE       = r'ELSE'
    ENDDO      = r'ENDDO'
    ENDFOR     = r'ENDFOR'
    ENDIF      = r'ENDIF'
    ENDWHILE   = r'ENDWHILE'
    END        = r'END'
    FOR        = r'FOR'
    FROM       = r'FROM'
    IF         = r'IF'
    IN         = r'IN'
    READ       = r'READ'
    THEN       = r'THEN'
    TO         = r'TO'
    WHILE      = r'WHILE'
    WRITE      = r'WRITE'

    ASSIGN     = r':='
    PLUS       = r'[+]'
    MINUS      = r'[-]'
    ASTERISK   = r'[*]'
    FSLASH     = r'[/]'
    PERCENT    = r'[%]'

    EQ         = r'='
    NEQ        = r'!='
    LEQ        = r'<='
    GEQ        = r'>='
    LT         = r'<'
    GT         = r'>'

    LPAREN     = r'[(]'
    RPAREN     = r'[)]'
    SEMICOLON  = r'[;]'
    COLON      = r'[:]'

    PIDENTIFIER = r'[_a-z]+'
    NUM         = r'\d+'


class Parser(sly.Parser):
    # Imported token list
    tokens = Lexer.tokens

    def __init__(self, compilercontext, **kwargs):
        super().__init__(**kwargs)
        self.compilercontext = compilercontext

    # Grammar rules:
    @_('DECLARE declarations IN commands END')
    def program(self, p):
        # Finalize AST
        self.compilercontext.parse_ast(p.commands)

    @_('declarations PIDENTIFIER SEMICOLON')
    def declarations(self, p):
        self.compilercontext.declare_var(p.PIDENTIFIER)

    @_('declarations PIDENTIFIER LPAREN NUM COLON NUM RPAREN SEMICOLON')
    def declarations(self, p):
        self.compilercontext.declare_array(p.PIDENTIFIER, int(p.NUM0), int(p.NUM1))

    @_('')
    def declarations(self, p):
        # If required, initialize global contexts here
        pass

    @_('commands command')
    def commands(self, p):
        return p.commands + [p.command]

    @_('command')
    def commands(self, p):
        return [p.command]

    @_('identifier ASSIGN expression SEMICOLON')
    def command(self, p):
        return ('ASSIGN', p.identifier, p.expression)

    @_('IF condition THEN commands ELSE commands ENDIF')
    def command(self, p):
        return ('IF', p.condition, p.commands0, p.commands1)

    @_('IF condition THEN commands ENDIF')
    def command(self, p):
        return ('IF', p.condition, p.commands, [])

    @_('WHILE condition DO commands ENDWHILE')
    def command(self, p):
        return ('WHILE', p.condition, p.commands)

    @_('DO commands WHILE condition ENDDO')
    def command(self, p):
        return ('DO', p.condition, p.commands)

    @_('FOR PIDENTIFIER FROM value TO value DO commands ENDFOR')
    def command(self, p):
        return ('FOR', 1, p.PIDENTIFIER, p.value0, p.value1, p.commands)

    @_('FOR PIDENTIFIER FROM value DOWNTO value DO commands ENDFOR')
    def command(self, p):
        return ('FOR', -1, p.PIDENTIFIER, p.value0, p.value1, p.commands)

    @_('READ identifier SEMICOLON')
    def command(self, p):
        return ('READ', p.identifier)

    @_('WRITE value SEMICOLON')
    def command(self, p):
        return ('WRITE', p.value)

    @_('value')
    def expression(self, p):
        return ('VALUE', p.value)

    @_('value PLUS value')
    def expression(self, p):
        return ('ADD', p.value0, p.value1)

    @_('value MINUS value')
    def expression(self, p):
        return ('SUB', p.value0, p.value1)

    @_('value ASTERISK value')
    def expression(self, p):
        return ('MUL', p.value0, p.value1)

    @_('value FSLASH value')
    def expression(self, p):
        return ('DIV', p.value0, p.value1)

    @_('value PERCENT value')
    def expression(self, p):
        return ('REM', p.value0, p.value1)

    @_('value EQ value')
    def condition(self, p):
        return ('EQ', p.value0, p.value1)

    @_('value NEQ value')
    def condition(self, p):
        return ('NEQ', p.value0, p.value1)

    @_('value LT value')
    def condition(self, p):
        return ('LT', p.value0, p.value1)

    @_('value GT value')
    def condition(self, p):
        return ('GT', p.value0, p.value1)

    @_('value LEQ value')
    def condition(self, p):
        return ('LEQ', p.value0, p.value1)

    @_('value GEQ value')
    def condition(self, p):
        return ('GEQ', p.value0, p.value1)

    @_('NUM')
    def value(self, p):
        return ('NUM', int(p.NUM))

    @_('identifier')
    def value(self, p):
        return p.identifier

    @_('PIDENTIFIER')
    def identifier(self, p):
        return ('VAR', p.PIDENTIFIER)

    @_('PIDENTIFIER LPAREN PIDENTIFIER RPAREN')
    def identifier(self, p):
        return ('ARRX', p.PIDENTIFIER0, p.PIDENTIFIER1)

    @_('PIDENTIFIER LPAREN NUM RPAREN')
    def identifier(self, p):
        return ('ARRI', p.PIDENTIFIER, int(p.NUM))


if __name__ == '__main__':
    context = CompilerContext()
    lexer = Lexer()
    parser = Parser(context)

    with open(sys.argv[1], 'r') as f:
        parser.parse(lexer.tokenize(f.read()))

    print(">>> Initial IR")
    context.dump_ir()

    context.run_iropt()
    print(">>> Post-IROpt")
    context.dump_ir()

    # TODO: Uncomment if/when this will be different from Post-IROpt
    # print(">>> Final IR")
    # context.dump_ir()

    context.run_isel()
    print(">>> Post-ISel")
    context.dump_mir()

    context.run_miropt()
    print(">>> Post-MIROpt")
    context.dump_mir()

    context.run_regalloc()
    print(">>> Post-RA")
    context.dump_mir()

    context.run_malloc()
    print(">>> Post-Malloc")
    context.dump_mir()

    context.run_miropt()
    print(">>> Post-MIROpt")
    context.dump_mir()

    context.run_legalize()
    print(">>> Post-Legalize")
    context.dump_mir()

    # TODO: IMHO, at this point opts can only make it worse,
    # introduce bugs, etc; if we have a special case for those
    # "safe" opts, we can add them separately, but not with the regular
    # run_miropt.
    # context.run_miropt()
    # print(">>> Post-MIROpt")
    # context.dump_mir()

    print(">>> CodeGen")
    context.run_codegen(sys.stdout)

    try:
        with open(sys.argv[2], 'w') as f:
            context.run_codegen(f)
    except IndexError:
        pass