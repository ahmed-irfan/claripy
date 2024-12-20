from __future__ import annotations

import ctypes
from functools import reduce
import logging
import numbers
import operator
import os
import threading
import weakref

from cachetools import LRUCache
import yices

from claripy.annotation import Annotation
from claripy.ast.bool import Bool, BoolS, BoolV, If, Not, Or, And
from claripy.ast.bv import BV, BVS, BVV
from claripy.backends.backend import Backend
from claripy.errors import BackendError, ClaripyOperationError, ClaripySolverInterruptError, ClaripyYicesError
from claripy.operations import backend_operations, bound_ops


log = logging.getLogger(__name__)

ALL_YICES_CONTEXTS = weakref.WeakSet()

try:
    import __pypy__

    _is_pypy = True
except ImportError:
    _is_pypy = False

"""
Wrapper around the Yices terms, which are simply ints.
"""
class YicesTerm(object):
    def __init__(self, term):
        self._ast = term
    
    def __hash__(self):
        return self._ast

    @property
    def ast(self):
        return self._ast
    


def condom(f):
    def yices_condom(*args, **kwargs):
        """
        The Yices condom intercepts YicesExceptions and throws a ClaripyYicesError instead.
        """
        try:
            return f(*args, **kwargs)
        except yices.YicesException as ye:
            raise ClaripyYicesError from ye

    return yices_condom


class SmartLRUCache(LRUCache):
    def __init__(self, maxsize, getsizeof=None, evict=None):
        LRUCache.__init__(self, maxsize, getsizeof=getsizeof)
        self._evict = evict

    def popitem(self):
        key, val = LRUCache.popitem(self)
        if self._evict:
            self._evict(key, val)
        return key, val

def _add_memory_pressure(p):
    """
    PyPy's garbage collector is not aware of memory uses happening inside native code. When performing memory-intensive
    tasks in native code, the memory pressure that PyPy observes can greatly deviate from the actual memory pressure.
    We must manually add sufficient memory pressure to account for the "missing" portion.

    This is not a problem for CPython since its GC is based on reference counting.
    """

    global _is_pypy  # pylint:disable=global-variable-not-assigned
    if _is_pypy:
        __pypy__.add_memory_pressure(p)


class BackendYices(Backend):
    _split_on = ("And", "Or")
    
    def __init__(self, reuse_yices_solver=None, ast_cache_size=10000):
        Backend.__init__(self, solver_required=True)

        # Per-thread Yices solver
        # This setting is treated as a global setting and is not supposed to be changed during runtime, unless you know
        # what you are doing.
        if reuse_yices_solver is None:
            reuse_yices_solver = os.environ.get("REUSE_YICES_SOLVER", "False").lower() in {"1", "true", "yes", "y"}
        self.reuse_yices_solver = reuse_yices_solver

        self._ast_cache_size = ast_cache_size

        all_ops = backend_operations - {"FPV", "StringV", "FPS", "StringS"}
        for o in all_ops - {"BVV", "BoolV", "BitVec"}:
            self._op_raw[o] = getattr(self, "_op_raw_" + o)
        self._op_raw["Xor"] = self._op_raw_Xor

        self._op_raw["__ge__"] = self._op_raw_UGE
        self._op_raw["__gt__"] = self._op_raw_UGT
        self._op_raw["__le__"] = self._op_raw_ULE
        self._op_raw["__lt__"] = self._op_raw_ULT
        
        self._op_raw["__eq__"] = self._op_raw_eq
        self._op_raw["__ne__"] = self._op_raw_ne

        self._op_raw["Reverse"] = self._op_raw_Reverse

        self._op_expr["BVS"] = self.BVS
        self._op_expr["BVV"] = self.BVV
        self._op_expr["BoolV"] = self.BoolV
        self._op_expr["BoolS"] = self.BoolS
        
        self._op_raw["__floordiv__"] = self._op_div
        self._op_raw["__mod__"] = self._op_mod

        self._op_raw["__add__"] = self._op_add
        self._op_raw["__pow__"] = self._op_pow
        self._op_raw["__lshift__"] = self._op_lshift
        self._op_raw["__rshift__"] = self._op_rshift

        self._op_raw["__or__"] = self._op_or
        self._op_raw["__and__"] = self._op_and

        # reduceable
        self._op_raw["__sub__"] = self._op_sub
        self._op_raw["__mul__"] = self._op_mul
        self._op_raw["__xor__"] = self._op_xor
        
        self.solve_count = 0
        self.timeout = 0
        self.memlimit = 0

        self.already_tracked = set() # boolean assumption names (as strings) 
        self.tracked_assumptions = [] # boolean assumption variables (without YicesTerm class wrapper)
        self.tracked_assumptions_map = {} # map from boolean assumptions to actual assertions (without YicesTerm class wrapper)
        self.tracked_assumptions_size_stack = [] # remember size of tracked_assumptions list (per push)

    
    @property
    def bvs_annotations(self) -> dict[bytes, tuple[Annotation, ...]]:
        if not hasattr(self._tls, "bvs_annotations"):
            self._tls.bvs_annotations = {}
        return self._tls.bvs_annotations
        
    @property
    def _c_uint64_p(self):
        try:
            return self._tls.c_uint64_p
        except AttributeError:
            # a pointer to get values out of Yices
            self._tls.c_uint64_p = ctypes.pointer(ctypes.c_uint64())

            return self._tls.c_uint64_p
        

    @property
    def _context(self):
        try:
            return self._tls.context
        except AttributeError:
            self._tls.context = yices.Context()
            ALL_YICES_CONTEXTS.add(self._tls.context)
            return self._tls.context
        
    @property
    def _ast_cache(self):
        try:
            return self._tls.ast_cache
        except AttributeError:
            self._tls.ast_cache = SmartLRUCache(self._ast_cache_size)
            return self._tls.ast_cache

    @property
    def _var_cache(self):
        try:
            return self._tls.var_cache
        except AttributeError:
            self._tls.var_cache = weakref.WeakValueDictionary()
            return self._tls.var_cache

    @property
    def _sym_cache(self):
        try:
            return self._tls.sym_cache
        except AttributeError:
            self._tls.sym_cache = weakref.WeakValueDictionary()
            return self._tls.sym_cache

    def downsize(self):
        Backend.downsize(self)

        self._ast_cache.clear()
        self._var_cache.clear()
        self._sym_cache.clear()

    def _name(self, o):  # pylint:disable=unused-argument
        log.warning("BackendYices.name() called. This is weird.")
        raise BackendError("name is not implemented yet")

    
    #
    # Core creation methods
    #

    @condom
    def BVS(self, ast):
        name = ast._encoded_name
        self.bvs_annotations[name] = ast.annotations
        size = ast.size()
        bv = yices.Types.bv_type(size)
        res = YicesTerm(yices.Terms.new_uninterpreted_term(bv, name))
        assert(res != None)
        return res

    @condom
    def BVV(self, ast):
        if ast.args[0] is None:
            raise BackendError("Yices can't handle empty BVVs")

        size = ast.size()
        return YicesTerm(yices.Terms.bvconst_integer(size, ast.args[0]))
    
    @condom
    def BoolS(self, ast):
        return YicesTerm(yices.Terms.new_uninterpreted_term(yices.Types.bool_type(), ast._encoded_name))
    
    @condom
    def BoolV(self, ast):
        if ast.args[0]:
            return YicesTerm(yices.Terms.true())
        else:
            return YicesTerm(yices.Terms.false())

    @condom
    def _convert(self, obj):  # pylint:disable=arguments-renamed
        if obj is True:
            return YicesTerm(yices.Terms.true())
        if obj is False:
            return YicesTerm(yices.Terms.false())
        if isinstance(obj, numbers.Number):
            return obj
        if isinstance(obj, YicesTerm):
            return obj
        log.debug("BackendYices encountered unexpected type %s", type(obj))
        raise BackendError(f"unexpected type {type(obj)} encountered in BackendYices")

    def call(self, *args, **kwargs):  # pylint;disable=arguments-renamed
        return Backend.call(self, *args, **kwargs)

    @condom
    def _abstract(self, t):
        return self._abstract_internal(t)

    @staticmethod
    def _yices_ast_hash(t):
        return t.ast

    def _abstract_internal(self, yterm, split_on=None):
        h = self._yices_ast_hash(yterm)
        try:
            cached_t, _ = self._ast_cache[h]
            return cached_t
        except KeyError:
            pass

        t = yterm.ast
        if t == yices.Terms.true():
            a = BoolV(True)
        elif t == yices.Terms.false():
            a =  BoolV(False)
        elif yices.Terms.is_atomic(t):
            ty = yices.Terms.type_of_term(t)
            if yices.Types.is_bitvector(ty):
                bv_size = yices.Terms.bitsize(t)
                assert(bv_size > 0)
                
                constructor = yices.Terms.constructor(t)
                if constructor == yices.Constructor.BV_CONSTANT:
                    bv_num = int("".join(str(i) for i in yices.Terms.bv_const_value(t))[::-1],2)
                    a =  BVV(bv_num, bv_size)
                if constructor == yices.Constructor.UNINTERPRETED_TERM:
                    symbol_name = yices.Terms.get_name(t)
                    annots = self.bvs_annotations.get(symbol_name, ())
                    a =  BVS(symbol_name, bv_size, explicit_name=True, annotations=annots)
            elif yices.Types.is_bool(ty):
                assert(yices.Terms.constructor(t) == yices.Constructor.UNINTERPRETED_TERM)
                symbol_name = yices.Terms.get_name(t)
                a =  BoolS(symbol_name, explicit_name=True)
            else:
                raise BackendError("Unknown Yices term type %d...?" & symbol_name)
        elif yices.Terms.is_composite(t):
            constructor = yices.Terms.constructor(t)
            num_children = yices.Terms.num_children(t)

            children = [self._abstract_internal(YicesTerm(yices.Terms.child(t, i))) for i in range(num_children)]

            if constructor == yices.Constructor.ITE_TERM:
                a = If(children[0], children[1], children[2])
            elif constructor == yices.Constructor.EQ_TERM:
                if yices.Terms.is_bool(yices.Terms.child(t, 0)):
                    a = Bool.__eq__(children[0], children[1])
                elif yices.Terms.is_bitvector(yices.Terms.child(t, 0)):
                    a = BV.__eq__(children[0], children[1])
                else:
                    raise BackendError("Yices backend does not support equality between type %d...?" % yices.Types.__str__(yices.Terms.type_of_term(yices.Terms.child(t, 0))))
            elif constructor == yices.Constructor.DISTINCT_TERM:
                if yices.Terms.is_bool(yices.Terms.child(t, 0)):
                    a = Bool.__ne__(children[0], children[1])
                elif yices.Terms.is_bitvector(yices.Terms.child(t, 0)):
                    a = BV.__ne__(children[0], children[1])
                else:
                    raise BackendError("Yices backend does not support distinct op between type %d...?" % yices.Types.__str__(yices.Terms.type_of_term(yices.Terms.child(t, 0))))
            elif constructor == yices.Constructor.NOT_TERM:
                a = Not((children[0],))
            elif constructor == yices.Constructor.OR_TERM:
                a = reduce(Or, children)
            elif constructor == yices.Constructor.XOR_TERM:
                a = Not(Or(reduce(And, children), Not(reduce(Or, children))))
            elif constructor == yices.Constructor.BV_ARRAY:
                a = BV.concat(tuple(children))
            elif constructor == yices.Constructor.BV_DIV:
                a = BV.__floordiv__(children[0], children[1])
            elif constructor == yices.Constructor.BV_REM:
                a = BV.__mod__(children[0], children[1])
            elif constructor == yices.Constructor.BV_SDIV:
                a = BV.SDiv(children[0], children[1])
            elif constructor == yices.Constructor.BV_SREM or constructor == yices.Constructor.BV_SMOD:
                a = BV.SMod(children[0], children[1])
            elif constructor == yices.Constructor.BV_SHL:
                a = BV.__lshift__(children[0], children[1])
            elif constructor == yices.Constructor.BV_LSHR:
                a = BV.LShR(children[1], children[1])
            elif constructor == yices.Constructor.BV_ASHR:
                a = BV.__rshift__(children[0], children[1])
            elif constructor == yices.Constructor.BV_GE_ATOM:
                a = BV.UGE(children[0], children[1])
            elif constructor == yices.Constructor.BV_SGE_ATOM:
                a = BV.SGE(children[0], children[1])
            else:
                raise BackendError("Yices backend does not support term %d...?" % yices.Terms.to_string(t))
        elif yices.Terms.is_projection(t):
            constructor = yices.Terms.constructor(t)
            num_children = yices.Terms.num_children(t)
            
            if constructor == yices.Constructor.BIT_TERM:
                i = yices.Terms.proj_index(t)
                a =  BV.Extract(self._abstract_internal(YicesTerm(yices.Terms.proj_arg(t))), i, i+1)
            else:
                raise BackendError("Yices backend does not support term %d...?" % yices.Terms.to_string(t))
        elif yices.Terms.is_bvsum(t):
            num_children = yices.Terms.num_children(t)
            args = []
            for i in range(num_children):
                (c, m) = yices.Terms.bvsum_component(t, i)
                c = int("".join(str(i) for i in c)[::-1],2)
                if m == yices.Terms.NULL_TERM:
                    args.append(c)
                else:
                    args.append(BV.__mul__(c, self._abstract_internal(YicesTerm(m))))
            a = reduce(BV.__add__, args)
        elif yices.Terms.is_product(t):
            num_children = yices.Terms.num_children(t)
            args = []
            for i in range(num_children):
                (x, e) = yices.Terms.product_component(t, i)
                m = [self._abstract_internal(x)] * e
                args.append(reduce(BV.__mul__, m))
            a =  reduce(BV.__mul__, args)
        else:
            raise BackendError("Yices backend does not support term %s...?" % yices.Terms.to_string(t))
            
        self._ast_cache[h] = (a, t)
        return a

    def _abstract_to_primitive(self, yterm):
        t = yterm.ast
        if t == yices.Terms.true():
            return True
        if t == yices.Terms.false():
            return False
        if yices.Terms.is_atomic(t):
            ty = yices.Terms.type_of_term(t)
            if yices.Types.is_bitvector(ty):
                bv_size = yices.Terms.bitsize(t)
                assert(bv_size > 0)
                constructor = yices.Terms.constructor(t)
                if constructor == yices.Constructor.BV_CONSTANT:
                    bv_num = int("".join(str(i) for i in yices.Terms.bv_const_value(t))[::-1],2)
                    return bv_num
        raise BackendError("Unable to abstract Yices object to Primitive")

    def solver(self, timeout=None, max_memory=None):    
        if not self.reuse_yices_solver or getattr(self._tls, "solver", None) is None:
            cfg = yices.Config()
            s = yices.Context(cfg)
            if threading.current_thread() != threading.main_thread():
                s.set(ctrl_c=False)
            _add_memory_pressure(1024 * 1024 * 10)
            if self.reuse_yices_solver:
                self._tls.solver = s
        else:
            # Load the existing Yices solver
            s = self._tls.solver
            self._yices_reset_context(s)

        # Configure timeouts and memout
        # TODO
        if timeout is not None:
            self.timeout = timeout
        if max_memory is not None:
            self.memlimit = max_memory
        
        return s

    def _bool_assump_name(self, name):
        return "bool_assump_" + name

    def _add(self, s, c, track=False):
        if track:
            for constraint in c:
                name = self._bool_assump_name(str(constraint.ast))
                if name not in self.already_tracked:
                    assump = yices.Terms.new_uninterpreted_term(yices.Types.bool_type(), name)
                    a = yices.Terms.implies(assump, constraint.ast)
                    self._yices_assert_formula(s, YicesTerm(a))
                    self.already_tracked.add(name)
                    self.tracked_assumptions.append(assump)
                    self.tracked_assumptions_map[assump] = constraint
        else:
            self._yices_assert_formulas(s, c)

    def add(self, s, c, track=False):
        converted = self.convert_list(c)
        if track:
            for a, nice_ast in zip(c, converted, strict=False):
                h = self._yices_ast_hash(nice_ast)
                self._ast_cache[h] = (a, nice_ast)
        return self._add(s, converted, track=track)

    def _unsat_core(self, s):
        cores = yices.Context.get_unsat_core(s)
        return [self.tracked_assumptions_map[c] for c in cores]

    @condom
    def _primitive_from_model(self, model, expr):
        v = yices.Model.get_value_as_term(model, expr.ast)
        return self._abstract_to_primitive(YicesTerm(v))


    def _generic_model(self, yices_model):
        """
        Converts a Yices model to a name->primitive dict.
        """
        model = {}
        defined_terms = yices.Model.collect_defined_terms(yices_model)
        for m in defined_terms:
            me = yices.Model.get_value_as_term(yices_model, m)
            model[m] = self._abstract_to_primitive(YicesTerm(me))

        return model


    def _yices_reset_context(self, solver):
        self.already_tracked.clear()
        self.tracked_assumptions.clear()
        self.tracked_assumptions_map.clear()
        self.tracked_assumptions_size_stack.clear()
        yices.Context.reset_context(solver)


    def _yices_assert_formula(self, solver, assertion):  
        yices.Context.assert_formula(solver, assertion.ast)


    def _yices_assert_formulas(self, solver, assertions):
        yices.Context.assert_formulas(solver, [a.ast for a in assertions])


    def _yices_check_context(self, solver, extra_constraints=[], occasion=""):
        log.debug("Doing a check! (%s)", occasion)

        assumps = self.tracked_assumptions + [e.ast for e in extra_constraints]
        result = yices.Context.check_context_with_assumptions(solver, None, assumps)

        if result == yices.Status.ERROR:
            raise ClaripyYicesError("solver error ")
        if result == yices.Status.INTERRUPTED:
            raise ClaripySolverInterruptError("Interrupted")
        if result == yices.Status.UNKNOWN:
            raise ClaripyYicesError("solver unknown ")
        return result == yices.Status.SAT
    
    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        self.solve_count += 1

        log.debug("Doing a check! (satisfiable)")
        
        if not self._yices_check_context(solver, list(extra_constraints), "satisfiable"):
            return False

        if model_callback is not None:
            model_callback(self._generic_model(yices.Model.from_context(solver, 1)))
        return True

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        results = self._batch_eval(
            [expr], n, extra_constraints=extra_constraints, solver=solver, model_callback=model_callback
        )

        # Unpack it
        return [v[0] for v in results]
    
    def _push(self, solver=None):
        yices.Context.push(solver)
        self.tracked_assumptions_size_stack.append(len(self.tracked_assumptions))

    def _pop(self, solver=None):
        yices.Context.pop(solver)
        assump_size = self.tracked_assumptions_size_stack.pop()
        self.tracked_assumptions = self.tracked_assumptions[:assump_size]
    
    @condom
    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
        result_values = []

        if n > 1:
            self._push(solver)

        for i in range(n):
            self.solve_count += 1
            if not self._yices_check_context(solver, list(extra_constraints), "batch_eval"):
                break
            model = yices.Model.from_context(solver, 1)

            # construct results
            r = []
            for expr in exprs:
                if not isinstance(expr, numbers.Number | bool):
                    v = YicesTerm(yices.Model.get_value_as_term(model, expr.ast))
                    r.append(v)
                else:
                    r.append(expr)

            # Append the solution to the result list
            if model_callback is not None:
                model_callback(self._generic_model(model))
            result_values.append(tuple([self._abstract_to_primitive(v) if isinstance(v, YicesTerm) else v for v in r]))

            # Construct the extra constraint so we don't get the same result anymore
            if i + 1 != n:
                l = [self._op_raw_eq(ex, ex_v) if not isinstance(ex, numbers.Number) else YicesTerm(yices.Terms.true()) for ex, ex_v in zip(exprs, r, strict=False)]
                self._yices_assert_formula(solver, self._op_raw_Not(self._op_raw_And(*l)))
                model = None

        if n > 1:
            self._pop(solver)

        return result_values
    
    def _extrema(self, is_max: bool, expr, extra_constraints, signed, solver, model_callback):
        """
        _max if is_max else _min
        """
        
        bv_size = yices.Terms.bitsize(expr.ast)
        lo = -(2 ** (bv_size - 1)) if signed else 0
        hi = 2 ** (bv_size - 1) - 1 if signed else 2 ** bv_size - 1

        constraints = extra_constraints
        comment = "max" if is_max else "min"

        GE = self._op_raw_SGE if signed else self._op_raw_UGE
        LE = self._op_raw_SLE if signed else self._op_raw_ULE

        while hi - lo > 1:
            middle = (lo + hi) // 2
            # l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)
            
            constraints.append(
                self._op_raw_And(GE(expr, YicesTerm(yices.Terms.bvconst_integer(bv_size, middle))), 
                                 LE(expr, YicesTerm(yices.Terms.bvconst_integer(bv_size, hi)))) if is_max 
                                 else self._op_raw_And(GE(expr, YicesTerm(yices.Terms.bvconst_integer(bv_size, lo))), 
                                                       LE(expr, YicesTerm(yices.Terms.bvconst_integer(bv_size, middle))))
            )

            self.solve_count += 1
            sat = self._yices_check_context(solver, constraints, comment)
            constraints.pop()
            if sat:
                log.debug("... still sat")
                if model_callback is not None:
                    model_callback(self._generic_model(yices.Model.from_context(solver, 1)))
            else:
                log.debug("... now unsat")
            if sat == is_max:
                lo = middle
            else:
                hi = middle

        constraints.append(self._op_raw_eq(expr, YicesTerm(yices.Terms.bvconst_integer(bv_size, hi)) if is_max 
                                           else YicesTerm(yices.Terms.bvconst_integer(bv_size, lo))))
        sat = self._yices_check_context(solver, constraints, comment)
        if sat and model_callback is not None:
            model_callback(self._generic_model(yices.Model.from_context(solver, 1)))
        return hi if sat == is_max else lo

    @condom
    def _min(self, expr, extra_constraints=(), signed=False, solver=None, model_callback=None):
        return self._extrema(False, expr, extra_constraints, signed, solver, model_callback)

    @condom
    def _max(self, expr, extra_constraints=(), signed=False, solver=None, model_callback=None):
        return self._extrema(True, expr, extra_constraints, signed, solver, model_callback)

    @condom
    def simplify(self, expr):
        expr_raw = self.convert(expr)
        return self._abstract(expr_raw)
    
    def _is_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        return e.ast == yices.Terms.false()

    def _is_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        return e.ast == yices.Terms.true()

    def _solution(self, expr, v, extra_constraints=(), solver=None, model_callback=None):
        assert(isinstance(expr, YicesTerm))
        bv_size = yices.Terms.bitsize(expr.ast)
        val_term = YicesTerm(yices.Terms.bvconst_integer(bv_size, v))
        return self._satisfiable(
            extra_constraints=(self._op_raw_eq(expr, val_term), *tuple(extra_constraints)), solver=solver, model_callback=model_callback
        )
    
    @staticmethod
    @condom
    def _op_div(a, b):
        return YicesTerm(yices.Terms.bvdiv(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_mod(a, b):
        return YicesTerm(yices.Terms.bvrem(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_add(*args):
        return YicesTerm(yices.Terms.bvsum([a.ast for a in args]))

    @staticmethod
    @condom
    def _op_pow(a, n):
        return YicesTerm(yices.Terms.power(a.ast, n))

    @staticmethod
    @condom
    def _op_lshift(a, b):
        return YicesTerm(yices.Terms.bvshl(a.ast, b.ast))
    
    @staticmethod
    @condom
    def _op_rshift(a, b):
        return YicesTerm(yices.Terms.bvashr(a.ast, b.ast))
    
    @staticmethod
    def _op_sub(*args):
        return YicesTerm(reduce(yices.Terms.bvsub, [a.ast for a in args]))

    @staticmethod
    def _op_mul(*args):
        return YicesTerm(reduce(yices.Terms.bvmul, [a.ast for a in args]))

    @staticmethod
    @condom
    def _op_or(*args):
        return YicesTerm(yices.Terms.bvor([a.ast for a in args]))

    @staticmethod
    def _op_xor(*args):
        return YicesTerm(reduce(yices.Terms.bvxor, [a.ast for a in args]))

    @staticmethod
    @condom
    def _op_and(*args):
        return YicesTerm(yices.Terms.bvand([a.ast for a in args]))
    
    @staticmethod
    @condom
    def _op_raw_And(*args):
        return YicesTerm(yices.Terms.yand([a.ast for a in args]))
    
    @staticmethod
    @condom
    def _op_raw_Xor(*args):
        return YicesTerm(yices.Terms.xor([a.ast for a in args]))

    @staticmethod
    @condom
    def _op_raw_Or(*args):
        return YicesTerm(yices.Terms.yor([a.ast for a in args]))

    @staticmethod
    @condom
    def _op_raw_Not(a):
        return YicesTerm(yices.Terms.ynot(a.ast))

    @staticmethod
    @condom
    def _op_raw_If(i, t, e):
        return YicesTerm(yices.Terms.ite(i.ast, t.ast, e.ast))

    @staticmethod
    @condom
    def _op_raw_Concat(*args):
        return YicesTerm(yices.Terms.bvconcat([a.ast for a in args]))
    
    @staticmethod
    @condom
    def _op_raw_Extract(high, low, a):
        return YicesTerm(yices.Terms.bvextract(a.ast, low, high))
    
    @staticmethod
    @condom
    def _op_raw_LShR(a, b):
        return YicesTerm(yices.Terms.bvlshr(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_RotateLeft(a, b):
        return YicesTerm(yices.Terms.rotate_left(a.ast, b))

    @staticmethod
    @condom
    def _op_raw_RotateRight(a, b):
        return YicesTerm(yices.Terms.rotate_right(a.ast, b))
    
    @staticmethod
    @condom
    def _op_raw_SignExt(n, a):
        return YicesTerm(yices.Terms.sign_extend(a.ast, n))

    @staticmethod
    @condom
    def _op_raw_UGE(a, b):
        return YicesTerm(yices.Terms.bvge_atom(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_UGT(a, b):
        return YicesTerm(yices.Terms.bvgt_atom(a.ast, b.ast))
    
    @staticmethod
    @condom
    def _op_raw_ULE(a, b):
        return YicesTerm(yices.Terms.bvle_atom(a.ast, b.ast))
    
    @staticmethod
    @condom
    def _op_raw_ULT(a, b):
        return YicesTerm(yices.Terms.bvlt_atom(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_eq(a, b):
        return YicesTerm(yices.Terms.eq(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_ne(a, b):
        return YicesTerm(yices.Terms.neq(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_ZeroExt(n, a):
        return YicesTerm(yices.Terms.zero_extend(a.ast, n))

    @staticmethod
    @condom
    def _op_raw_SMod(a, b):
        return YicesTerm(yices.Terms.bvsmod(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_Reverse(a):
        if a.size() == 8:
            return a
        if a.size() % 8 != 0:
            raise ClaripyOperationError("can't reverse non-byte sized bitvectors")
        return BackendYices._op_raw_Concat(*[BackendYices._op_raw_Extract(i + 7, i, a) for i in range(0, a.size(), 8)])

    @staticmethod
    @condom
    def _op_raw_SLT(a, b):
        return YicesTerm(yices.Terms.bvslt_atom(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_SLE(a, b):
        return YicesTerm(yices.Terms.bvsle_atom(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_SGT(a, b):
        return YicesTerm(yices.Terms.bvsgt_atom(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_SGE(a, b):
        return YicesTerm(yices.Terms.bvsge_atom(a.ast, b.ast))

    @staticmethod
    @condom
    def _op_raw_SDiv(a, b):
        return YicesTerm(yices.Terms.bvsdiv(a.ast, b.ast))

    @staticmethod
    def _identical(a, b):
        return a.ast == b.ast
