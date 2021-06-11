from collections import defaultdict, Set
from fractions import Fraction
import sys

from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libc.stddef cimport wchar_t

from libcpp.pair cimport pair
from libcpp.set cimport set as c_set
from libcpp.string cimport string
from libcpp.vector cimport vector

from cvc5 cimport cout
from cvc5 cimport Datatype as c_Datatype
from cvc5 cimport DatatypeConstructor as c_DatatypeConstructor
from cvc5 cimport DatatypeConstructorDecl as c_DatatypeConstructorDecl
from cvc5 cimport DatatypeDecl as c_DatatypeDecl
from cvc5 cimport DatatypeSelector as c_DatatypeSelector
from cvc5 cimport Result as c_Result
from cvc5 cimport RoundingMode as c_RoundingMode
from cvc5 cimport Op as c_Op
from cvc5 cimport Solver as c_Solver
from cvc5 cimport Grammar as c_Grammar
from cvc5 cimport Sort as c_Sort
from cvc5 cimport ROUND_NEAREST_TIES_TO_EVEN, ROUND_TOWARD_POSITIVE
from cvc5 cimport ROUND_TOWARD_NEGATIVE, ROUND_TOWARD_ZERO
from cvc5 cimport ROUND_NEAREST_TIES_TO_AWAY
from cvc5 cimport Term as c_Term
from cvc5 cimport hash as c_hash
from cvc5 cimport wstring as c_wstring
from cvc5 cimport tuple as c_tuple
from cvc5 cimport get0, get1, get2
from cvc5kinds cimport Kind as c_Kind

cdef extern from "Python.h":
    wchar_t* PyUnicode_AsWideCharString(object, Py_ssize_t *)
    object PyUnicode_FromWideChar(const wchar_t*, Py_ssize_t)
    void PyMem_Free(void*)

################################## DECORATORS #################################
def expand_list_arg(num_req_args=0):
    '''
    Creates a decorator that looks at index num_req_args of the args,
    if it's a list, it expands it before calling the function.
    '''
    def decorator(func):
        def wrapper(owner, *args):
            if len(args) == num_req_args + 1 and \
               isinstance(args[num_req_args], list):
                args = list(args[:num_req_args]) + args[num_req_args]
            return func(owner, *args)
        return wrapper
    return decorator
###############################################################################

# Style Guidelines
### Using PEP-8 spacing recommendations
### Limit linewidth to 79 characters
### Break before binary operators
### surround top level functions and classes with two spaces
### separate methods by one space
### use spaces in functions sparingly to separate logical blocks
### can omit spaces between unrelated oneliners
### always use c++ default arguments
#### only use default args of None at python level

# References and pointers
# The Solver object holds a pointer to a c_Solver.
# This is because the assignment operator is deleted in the C++ API for solvers.
# Cython has a limitation where you can't stack allocate objects
# that have constructors with arguments:
# https://groups.google.com/forum/#!topic/cython-users/fuKd-nQLpBs.
# To get around that you can either have a nullary constructor and assignment
# or, use a pointer (which is what we chose).
# An additional complication of this is that to free up resources, you must
# know when to delete the object.
# Python will not follow the same scoping rules as in C++, so it must be
# able to reference count. To do this correctly, the solver must be a
# reference in the Python class for any class that keeps a pointer to
# the solver in C++ (to ensure the solver is not deleted before something
# that depends on it).


## Objects for hashing
cdef c_hash[c_Op] cophash = c_hash[c_Op]()
cdef c_hash[c_Sort] csorthash = c_hash[c_Sort]()
cdef c_hash[c_Term] ctermhash = c_hash[c_Term]()


cdef class Datatype:
    """Wrapper class for :cpp:class:`cvc5::api::Datatype`."""
    cdef c_Datatype cd
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.solver = solver

    def __getitem__(self, index):
        """Return a constructor by index or by name."""
        cdef DatatypeConstructor dc = DatatypeConstructor(self.solver)
        if isinstance(index, int) and index >= 0:
            dc.cdc = self.cd[(<int?> index)]
        elif isinstance(index, str):
            dc.cdc = self.cd[(<const string &> index.encode())]
        else:
            raise ValueError("Expecting a non-negative integer or string")
        return dc

    def getConstructor(self, str name):
        """Return a constructor by name."""
        cdef DatatypeConstructor dc = DatatypeConstructor(self.solver)
        dc.cdc = self.cd.getConstructor(name.encode())
        return dc

    def getConstructorTerm(self, str name):
        """:return: the term representing the datatype constructor with the given name (see :cpp:func:`Datatype::getConstructorTerm() <cvc5::api::Datatype::getConstructorTerm>`)."""
        cdef Term term = Term(self.solver)
        term.cterm = self.cd.getConstructorTerm(name.encode())
        return term

    def getSelector(self, str name):
        """Return a selector by name."""
        cdef DatatypeSelector ds = DatatypeSelector(self.solver)
        ds.cds = self.cd.getSelector(name.encode())
        return ds

    def getName(self):
        return self.cd.getName().decode()

    def getNumConstructors(self):
        """:return: number of constructors."""
        return self.cd.getNumConstructors()

    def isParametric(self):
        """:return: whether this datatype is parametric."""
        return self.cd.isParametric()

    def isCodatatype(self):
        """:return: whether this datatype corresponds to a co-datatype."""
        return self.cd.isCodatatype()

    def isTuple(self):
        """:return: whether this datatype corresponds to a tuple."""
        return self.cd.isTuple()

    def isRecord(self):
        """:return: whether this datatype corresponds to a record."""
        return self.cd.isRecord()

    def isFinite(self):
        """:return: whether this datatype is finite."""
        return self.cd.isFinite()

    def isWellFounded(self):
        """:return: whether this datatype is well-founded (see :cpp:func:`Datatype::isWellFounded() <cvc5::api::Datatype::isWellFounded>`)."""
        return self.cd.isWellFounded()

    def hasNestedRecursion(self):
        """:return: whether this datatype has nested recursion (see :cpp:func:`Datatype::hasNestedRecursion() <cvc5::api::Datatype::hasNestedRecursion>`)."""
        return self.cd.hasNestedRecursion()

    def __str__(self):
        return self.cd.toString().decode()

    def __repr__(self):
        return self.cd.toString().decode()

    def __iter__(self):
        for ci in self.cd:
            dc = DatatypeConstructor(self.solver)
            dc.cdc = ci
            yield dc


cdef class DatatypeConstructor:
    cdef c_DatatypeConstructor cdc
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.cdc = c_DatatypeConstructor()
        self.solver = solver

    def __getitem__(self, index):
        cdef DatatypeSelector ds = DatatypeSelector(self.solver)
        if isinstance(index, int) and index >= 0:
            ds.cds = self.cdc[(<int?> index)]
        elif isinstance(index, str):
            ds.cds = self.cdc[(<const string &> index.encode())]
        else:
            raise ValueError("Expecting a non-negative integer or string")
        return ds

    def getName(self):
        return self.cdc.getName().decode()

    def getConstructorTerm(self):
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getConstructorTerm()
        return term

    def getSpecializedConstructorTerm(self, Sort retSort):
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getSpecializedConstructorTerm(retSort.csort)
        return term

    def getTesterTerm(self):
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getTesterTerm()
        return term

    def getNumSelectors(self):
        return self.cdc.getNumSelectors()

    def getSelector(self, str name):
        cdef DatatypeSelector ds = DatatypeSelector(self.solver)
        ds.cds = self.cdc.getSelector(name.encode())
        return ds

    def getSelectorTerm(self, str name):
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getSelectorTerm(name.encode())
        return term

    def __str__(self):
        return self.cdc.toString().decode()

    def __repr__(self):
        return self.cdc.toString().decode()

    def __iter__(self):
        for ci in self.cdc:
            ds = DatatypeSelector(self.solver)
            ds.cds = ci
            yield ds


cdef class DatatypeConstructorDecl:
    cdef c_DatatypeConstructorDecl cddc
    cdef Solver solver

    def __cinit__(self, Solver solver):
        self.solver = solver

    def addSelector(self, str name, Sort sort):
        self.cddc.addSelector(name.encode(), sort.csort)

    def addSelectorSelf(self, str name):
        self.cddc.addSelectorSelf(name.encode())

    def __str__(self):
        return self.cddc.toString().decode()

    def __repr__(self):
        return self.cddc.toString().decode()


cdef class DatatypeDecl:
    cdef c_DatatypeDecl cdd
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.solver = solver

    def addConstructor(self, DatatypeConstructorDecl ctor):
        self.cdd.addConstructor(ctor.cddc)

    def getNumConstructors(self):
        return self.cdd.getNumConstructors()

    def isParametric(self):
        return self.cdd.isParametric()

    def getName(self):
        return self.cdd.getName().decode()

    def __str__(self):
        return self.cdd.toString().decode()

    def __repr__(self):
        return self.cdd.toString().decode()


cdef class DatatypeSelector:
    cdef c_DatatypeSelector cds
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.cds = c_DatatypeSelector()
        self.solver = solver

    def getName(self):
        return self.cds.getName().decode()

    def getSelectorTerm(self):
        cdef Term term = Term(self.solver)
        term.cterm = self.cds.getSelectorTerm()
        return term

    def getUpdaterTerm(self):
        cdef Term term = Term(self.solver)
        term.cterm = self.cds.getUpdaterTerm()
        return term

    def getRangeSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.cds.getRangeSort()
        return sort

    def __str__(self):
        return self.cds.toString().decode()

    def __repr__(self):
        return self.cds.toString().decode()


cdef class Op:
    cdef c_Op cop
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.cop = c_Op()
        self.solver = solver

    def __eq__(self, Op other):
        return self.cop == other.cop

    def __ne__(self, Op other):
        return self.cop != other.cop

    def __str__(self):
        return self.cop.toString().decode()

    def __repr__(self):
        return self.cop.toString().decode()

    def __hash__(self):
        return cophash(self.cop)

    def getKind(self):
        return kind(<int> self.cop.getKind())
    
    def isIndexed(self):
        return self.cop.isIndexed()

    def isNull(self):
        return self.cop.isNull()

    def getIndices(self):
        indices = None
        try:
            indices = self.cop.getIndices[string]()
        except:
            pass

        try:
            indices = self.cop.getIndices[uint32_t]()
        except:
            pass

        try:
            indices = self.cop.getIndices[pair[uint32_t, uint32_t]]()
        except:
            pass

        if indices is None:
            raise RuntimeError("Unable to retrieve indices from {}".format(self))

        return indices

cdef class Grammar:
    cdef c_Grammar  cgrammar
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.solver = solver
        self.cgrammar = c_Grammar()

    def addRule(self, Term ntSymbol, Term rule):
        self.cgrammar.addRule(ntSymbol.cterm, rule.cterm)

    def addAnyConstant(self, Term ntSymbol):
        self.cgrammar.addAnyConstant(ntSymbol.cterm)

    def addAnyVariable(self, Term ntSymbol):
        self.cgrammar.addAnyVariable(ntSymbol.cterm)

    def addRules(self, Term ntSymbol, rules):
        cdef vector[c_Term] crules
        for r in rules:
            crules.push_back((<Term?> r).cterm)
        self.cgrammar.addRules(ntSymbol.cterm, crules)

cdef class Result:
    cdef c_Result cr
    def __cinit__(self):
        # gets populated by solver
        self.cr = c_Result()

    def isNull(self):
        return self.cr.isNull()

    def isSat(self):
        return self.cr.isSat()

    def isUnsat(self):
        return self.cr.isUnsat()

    def isSatUnknown(self):
        return self.cr.isSatUnknown()

    def isEntailed(self):
        return self.cr.isEntailed()

    def isNotEntailed(self):
        return self.cr.isNotEntailed()

    def isEntailmentUnknown(self):
        return self.cr.isEntailmentUnknown()

    def __eq__(self, Result other):
        return self.cr == other.cr

    def __ne__(self, Result other):
        return self.cr != other.cr

    def getUnknownExplanation(self):
        return self.cr.getUnknownExplanation().decode()

    def __str__(self):
        return self.cr.toString().decode()

    def __repr__(self):
        return self.cr.toString().decode()


cdef class RoundingMode:
    cdef c_RoundingMode crm
    cdef str name
    def __cinit__(self, int rm):
        # crm always assigned externally
        self.crm = <c_RoundingMode> rm
        self.name = __rounding_modes[rm]

    def __eq__(self, RoundingMode other):
        return (<int> self.crm) == (<int> other.crm)

    def __ne__(self, RoundingMode other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((<int> self.crm, self.name))

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


cdef class Solver:
    cdef c_Solver* csolver

    def __cinit__(self):
        self.csolver = new c_Solver(NULL)

    def __dealloc__(self):
        del self.csolver

    def supportsFloatingPoint(self):
        return self.csolver.supportsFloatingPoint()

    def getBooleanSort(self):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getBooleanSort()
        return sort

    def getIntegerSort(self):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getIntegerSort()
        return sort

    def getRealSort(self):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getRealSort()
        return sort

    def getRegExpSort(self):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getRegExpSort()
        return sort

    def getRoundingModeSort(self):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getRoundingModeSort()
        return sort

    def getStringSort(self):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getStringSort()
        return sort

    def mkArraySort(self, Sort indexSort, Sort elemSort):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkArraySort(indexSort.csort, elemSort.csort)
        return sort

    def mkBitVectorSort(self, uint32_t size):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkBitVectorSort(size)
        return sort

    def mkFloatingPointSort(self, uint32_t exp, uint32_t sig):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkFloatingPointSort(exp, sig)
        return sort

    def mkDatatypeSort(self, DatatypeDecl dtypedecl):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkDatatypeSort(dtypedecl.cdd)
        return sort

    def mkDatatypeSorts(self, list dtypedecls, unresolvedSorts = None):
        """:return: A list of datatype sorts that correspond to dtypedecls and unresolvedSorts"""
        if unresolvedSorts == None:
            unresolvedSorts = set([])
        else:
            assert isinstance(unresolvedSorts, Set)

        sorts = []
        cdef vector[c_DatatypeDecl] decls
        for decl in dtypedecls:
            decls.push_back((<DatatypeDecl?> decl).cdd)

        cdef c_set[c_Sort] usorts
        for usort in unresolvedSorts:
            usorts.insert((<Sort?> usort).csort)

        csorts = self.csolver.mkDatatypeSorts(
            <const vector[c_DatatypeDecl]&> decls, <const c_set[c_Sort]&> usorts)
        for csort in csorts:
          sort = Sort(self)
          sort.csort = csort
          sorts.append(sort)

        return sorts

    def mkFunctionSort(self, sorts, Sort codomain):

        cdef Sort sort = Sort(self)
        # populate a vector with dereferenced c_Sorts
        cdef vector[c_Sort] v

        if isinstance(sorts, Sort):
            sort.csort = self.csolver.mkFunctionSort((<Sort?> sorts).csort,
                                                     codomain.csort)
        elif isinstance(sorts, list):
            for s in sorts:
                v.push_back((<Sort?>s).csort)

            sort.csort = self.csolver.mkFunctionSort(<const vector[c_Sort]&> v,
                                                      codomain.csort)
        return sort

    def mkParamSort(self, symbolname):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkParamSort(symbolname.encode())
        return sort

    @expand_list_arg(num_req_args=0)
    def mkPredicateSort(self, *sorts):
        '''
        Supports the following arguments:
                 Sort mkPredicateSort(List[Sort] sorts)

                 where sorts can also be comma-separated arguments of
                  type Sort
        '''
        cdef Sort sort = Sort(self)
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        sort.csort = self.csolver.mkPredicateSort(<const vector[c_Sort]&> v)
        return sort

    @expand_list_arg(num_req_args=0)
    def mkRecordSort(self, *fields):
        '''
        Supports the following arguments:
                Sort mkRecordSort(List[Tuple[str, Sort]] fields)

                  where fields can also be comma-separated arguments of
          type Tuple[str, Sort]
        '''
        cdef Sort sort = Sort(self)
        cdef vector[pair[string, c_Sort]] v
        cdef pair[string, c_Sort] p
        for f in fields:
            name, sortarg = f
            name = name.encode()
            p = pair[string, c_Sort](<string?> name, (<Sort?> sortarg).csort)
            v.push_back(p)
        sort.csort = self.csolver.mkRecordSort(
            <const vector[pair[string, c_Sort]] &> v)
        return sort

    def mkSetSort(self, Sort elemSort):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkSetSort(elemSort.csort)
        return sort

    def mkBagSort(self, Sort elemSort):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkBagSort(elemSort.csort)
        return sort

    def mkSequenceSort(self, Sort elemSort):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkSequenceSort(elemSort.csort)
        return sort

    def mkUninterpretedSort(self, str name):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkUninterpretedSort(name.encode())
        return sort

    def mkSortConstructorSort(self, str symbol, size_t arity):
        cdef Sort sort = Sort(self)
        sort.csort =self.csolver.mkSortConstructorSort(symbol.encode(), arity)
        return sort

    @expand_list_arg(num_req_args=0)
    def mkTupleSort(self, *sorts):
        '''
           Supports the following arguments:
                Sort mkTupleSort(List[Sort] sorts)

                 where sorts can also be comma-separated arguments of
                 type Sort
        '''
        cdef Sort sort = Sort(self)
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        sort.csort = self.csolver.mkTupleSort(v)
        return sort

    @expand_list_arg(num_req_args=1)
    def mkTerm(self, kind_or_op, *args):
        '''
            Supports the following arguments:
                    Term mkTerm(Kind kind)
                    Term mkTerm(Kind kind, Op child1, List[Term] children)
                    Term mkTerm(Kind kind, List[Term] children)

                where List[Term] can also be comma-separated arguments
        '''
        cdef Term term = Term(self)
        cdef vector[c_Term] v

        op = kind_or_op
        if isinstance(kind_or_op, kind):
            op = self.mkOp(kind_or_op)

        if len(args) == 0:
            term.cterm = self.csolver.mkTerm((<Op?> op).cop)
        else:
            for a in args:
                v.push_back((<Term?> a).cterm)
            term.cterm = self.csolver.mkTerm((<Op?> op).cop, v)
        return term

    def mkTuple(self, sorts, terms):
        cdef vector[c_Sort] csorts
        cdef vector[c_Term] cterms

        for s in sorts:
            csorts.push_back((<Sort?> s).csort)
        for s in terms:
            cterms.push_back((<Term?> s).cterm)
        cdef Term result = Term(self)
        result.cterm = self.csolver.mkTuple(csorts, cterms)
        return result


    def mkOp(self, kind k, arg0=None, arg1 = None):
        '''
        Supports the following uses:
                Op mkOp(Kind kind)
                Op mkOp(Kind kind, Kind k)
                Op mkOp(Kind kind, const string& arg)
                Op mkOp(Kind kind, uint32_t arg)
                Op mkOp(Kind kind, uint32_t arg0, uint32_t arg1)
        '''
        cdef Op op = Op(self)

        if arg0 is None:
            op.cop = self.csolver.mkOp(k.k)
        elif arg1 is None:
            if isinstance(arg0, kind):
                op.cop = self.csolver.mkOp(k.k, (<kind?> arg0).k)
            elif isinstance(arg0, str):
                op.cop = self.csolver.mkOp(k.k,
                                           <const string &>
                                           arg0.encode())
            elif isinstance(arg0, int):
                op.cop = self.csolver.mkOp(k.k, <int?> arg0)
            else:
                raise ValueError("Unsupported signature"
                                 " mkOp: {}".format(" X ".join([str(k), str(arg0)])))
        else:
            if isinstance(arg0, int) and isinstance(arg1, int):
                op.cop = self.csolver.mkOp(k.k, <int> arg0,
                                                       <int> arg1)
            else:
                raise ValueError("Unsupported signature"
                                 " mkOp: {}".format(" X ".join([k, arg0, arg1])))
        return op

    def mkTrue(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkTrue()
        return term

    def mkFalse(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFalse()
        return term

    def mkBoolean(self, bint val):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkBoolean(val)
        return term

    def mkPi(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkPi()
        return term

    def mkInteger(self, val):
        cdef Term term = Term(self)
        if isinstance(val, str):
            term.cterm = self.csolver.mkInteger(<const string &> str(val).encode())
        else:
            assert(isinstance(val, int))
            term.cterm = self.csolver.mkInteger((<int?> val))
        return term

    def mkReal(self, val, den=None):
        '''
        Make a real number term.

        Really, makes a rational term.

        Can be used in various forms.
        * Given a string "N/D" constructs the corresponding rational.
        * Given a string "W.D" constructs the reduction of (W * P + D)/P, where
          P is the appropriate power of 10.
        * Given a float f, constructs the rational matching f's string
          representation. This means that mkReal(0.3) gives 3/10 and not the
          IEEE-754 approximation of 3/10.
        * Given a string "W" or an integer, constructs that integer.
        * Given two strings and/or integers N and D, constructs N/D.
        '''
        cdef Term term = Term(self)
        if den is None:
            term.cterm = self.csolver.mkReal(str(val).encode())
        else:
            if not isinstance(val, int) or not isinstance(den, int):
                raise ValueError("Expecting integers when"
                                 " constructing a rational"
                                 " but got: {}".format((val, den)))
            term.cterm = self.csolver.mkReal("{}/{}".format(val, den).encode())
        return term

    def mkRegexpEmpty(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRegexpEmpty()
        return term

    def mkRegexpSigma(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRegexpSigma()
        return term

    def mkEmptySet(self, Sort s):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkEmptySet(s.csort)
        return term


    def mkSepNil(self, Sort sort):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkSepNil(sort.csort)
        return term

    def mkString(self, str s):
        cdef Term term = Term(self)
        cdef Py_ssize_t size
        cdef wchar_t* tmp = PyUnicode_AsWideCharString(s, &size)
        term.cterm = self.csolver.mkString(c_wstring(tmp, size))
        PyMem_Free(tmp)
        return term

    def mkEmptySequence(self, Sort sort):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkEmptySequence(sort.csort)
        return term

    def mkUniverseSet(self, Sort sort):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkUniverseSet(sort.csort)
        return term

    @expand_list_arg(num_req_args=0)
    def mkBitVector(self, *args):
        '''
            Supports the following arguments:
            Term mkBitVector(int size, int val=0)
            Term mkBitVector(string val, int base = 2)
            Term mkBitVector(int size, string val, int base)
         '''
        cdef Term term = Term(self)
        if len(args) == 1:
            size_or_val = args[0]
            if isinstance(args[0], int):
                size = args[0]
                term.cterm = self.csolver.mkBitVector(<uint32_t> size)
            else:
                assert isinstance(args[0], str)
                val = args[0]
                term.cterm = self.csolver.mkBitVector(<const string&> str(val).encode())
        elif len(args) == 2:
            if isinstance(args[0], int):
                size = args[0]
                assert isinstance(args[1], int)
                val = args[1]
                term.cterm = self.csolver.mkBitVector(<uint32_t> size, <uint32_t> val)
            else:
                assert isinstance(args[0], str)
                assert isinstance(args[1], int)
                val = args[0]
                base = args[1]
                term.cterm = self.csolver.mkBitVector(<const string&> str(val).encode(), <uint32_t> base)
        elif len(args) == 3:
                assert isinstance(args[0], int)
                assert isinstance(args[1], str)
                assert isinstance(args[2], int)
                size = args[0]
                val = args[1]
                base = args[2]
                term.cterm = self.csolver.mkBitVector(<uint32_t> size, <const string&> str(val).encode(), <uint32_t> base)
        return term


    def mkBitVector(self, size_or_str, val = None):
        cdef Term term = Term(self)
        if isinstance(size_or_str, int):
            if val is None:
                term.cterm = self.csolver.mkBitVector(<uint32_t> size_or_str)
            else:
                term.cterm = self.csolver.mkBitVector(<uint32_t> size_or_str,
                                                      <const string &> str(val).encode(),
                                                      10)
        elif isinstance(size_or_str, str):
            # handle default value
            if val is None:
                term.cterm = self.csolver.mkBitVector(
                    <const string &> size_or_str.encode())
            else:
                term.cterm = self.csolver.mkBitVector(
                    <const string &> size_or_str.encode(), <uint32_t> val)
        else:
            raise ValueError("Unexpected inputs {} to"
                             " mkBitVector".format((size_or_str, val)))
        return term

    def mkConstArray(self, Sort sort, Term val):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkConstArray(sort.csort, val.cterm)
        return term

    def mkPosInf(self, int exp, int sig):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkPosInf(exp, sig)
        return term

    def mkNegInf(self, int exp, int sig):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkNegInf(exp, sig)
        return term

    def mkNaN(self, int exp, int sig):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkNaN(exp, sig)
        return term

    def mkPosZero(self, int exp, int sig):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkPosZero(exp, sig)
        return term

    def mkNegZero(self, int exp, int sig):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkNegZero(exp, sig)
        return term

    def mkRoundingMode(self, RoundingMode rm):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRoundingMode(<c_RoundingMode> rm.crm)
        return term

    def mkUninterpretedConst(self, Sort sort, int index):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkUninterpretedConst(sort.csort, index)
        return term

    def mkAbstractValue(self, index):
        cdef Term term = Term(self)
        try:
            term.cterm = self.csolver.mkAbstractValue(str(index).encode())
        except:
            raise ValueError("mkAbstractValue expects a str representing a number"
                             " or an int, but got{}".format(index))
        return term

    def mkFloatingPoint(self, int exp, int sig, Term val):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPoint(exp, sig, val.cterm)
        return term

    def mkConst(self, Sort sort, symbol=None):
        cdef Term term = Term(self)
        if symbol is None:
            term.cterm = self.csolver.mkConst(sort.csort)
        else:
            term.cterm = self.csolver.mkConst(sort.csort,
                                            (<str?> symbol).encode())
        return term

    def mkVar(self, Sort sort, symbol=None):
        cdef Term term = Term(self)
        if symbol is None:
            term.cterm = self.csolver.mkVar(sort.csort)
        else:
            term.cterm = self.csolver.mkVar(sort.csort,
                                            (<str?> symbol).encode())
        return term

    def mkDatatypeConstructorDecl(self, str name):
        cdef DatatypeConstructorDecl ddc = DatatypeConstructorDecl(self)
        ddc.cddc = self.csolver.mkDatatypeConstructorDecl(name.encode())
        return ddc

    def mkDatatypeDecl(self, str name, sorts_or_bool=None, isCoDatatype=None):
        cdef DatatypeDecl dd = DatatypeDecl(self)
        cdef vector[c_Sort] v

        # argument cases
        if sorts_or_bool is None and isCoDatatype is None:
            dd.cdd = self.csolver.mkDatatypeDecl(name.encode())
        elif sorts_or_bool is not None and isCoDatatype is None:
            if isinstance(sorts_or_bool, bool):
                dd.cdd = self.csolver.mkDatatypeDecl(<const string &> name.encode(),
                                                     <bint> sorts_or_bool)
            elif isinstance(sorts_or_bool, Sort):
                dd.cdd = self.csolver.mkDatatypeDecl(<const string &> name.encode(),
                                                     (<Sort> sorts_or_bool).csort)
            elif isinstance(sorts_or_bool, list):
                for s in sorts_or_bool:
                    v.push_back((<Sort?> s).csort)
                dd.cdd = self.csolver.mkDatatypeDecl(<const string &> name.encode(),
                                                     <const vector[c_Sort]&> v)
            else:
                raise ValueError("Unhandled second argument type {}"
                                 .format(type(sorts_or_bool)))
        elif sorts_or_bool is not None and isCoDatatype is not None:
            if isinstance(sorts_or_bool, Sort):
                dd.cdd = self.csolver.mkDatatypeDecl(<const string &> name.encode(),
                                                     (<Sort> sorts_or_bool).csort,
                                                     <bint> isCoDatatype)
            elif isinstance(sorts_or_bool, list):
                for s in sorts_or_bool:
                    v.push_back((<Sort?> s).csort)
                dd.cdd = self.csolver.mkDatatypeDecl(<const string &> name.encode(),
                                                     <const vector[c_Sort]&> v,
                                                     <bint> isCoDatatype)
            else:
                raise ValueError("Unhandled second argument type {}"
                                 .format(type(sorts_or_bool)))
        else:
            raise ValueError("Can't create DatatypeDecl with {}".format([type(a)
                                                                         for a in [name,
                                                                                   sorts_or_bool,
                                                                                   isCoDatatype]]))

        return dd

    def simplify(self, Term t):
        cdef Term term = Term(self)
        term.cterm = self.csolver.simplify(t.cterm)
        return term

    def assertFormula(self, Term term):
        self.csolver.assertFormula(term.cterm)

    def checkSat(self):
        cdef Result r = Result()
        r.cr = self.csolver.checkSat()
        return r

    def mkSygusGrammar(self, boundVars, ntSymbols):
        cdef Grammar grammar = Grammar(self)
        cdef vector[c_Term] bvc
        cdef vector[c_Term] ntc
        for bv in boundVars:
            bvc.push_back((<Term?> bv).cterm)
        for nt in ntSymbols:
            ntc.push_back((<Term?> nt).cterm)
        grammar.cgrammar = self.csolver.mkSygusGrammar(<const vector[c_Term]&> bvc, <const vector[c_Term]&> ntc)
        return grammar

    def mkSygusVar(self, Sort sort, str symbol=""):
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkSygusVar(sort.csort, symbol.encode())
        return term

    def addSygusConstraint(self, Term t):
        self.csolver.addSygusConstraint(t.cterm)

    def addSygusInvConstraint(self, Term inv_f, Term pre_f, Term trans_f, Term post_f):
        self.csolver.addSygusInvConstraint(inv_f.cterm, pre_f.cterm, trans_f.cterm, post_f.cterm)

    def synthFun(self, str symbol, bound_vars, Sort sort, Grammar grammar=None):
        cdef Term term = Term(self)
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)
        if grammar is None:
          term.cterm = self.csolver.synthFun(symbol.encode(), <const vector[c_Term]&> v, sort.csort)
        else:
          term.cterm = self.csolver.synthFun(symbol.encode(), <const vector[c_Term]&> v, sort.csort, grammar.cgrammar)
        return term

    def checkSynth(self):
        cdef Result r = Result()
        r.cr = self.csolver.checkSynth()
        return r

    def getSynthSolution(self, Term term):
        cdef Term t = Term(self)
        t.cterm = self.csolver.getSynthSolution(term.cterm)
        return t

    def getSynthSolutions(self, list terms):
        result = []
        cdef vector[c_Term] vec
        for t in terms:
            vec.push_back((<Term?> t).cterm)
        cresult = self.csolver.getSynthSolutions(vec)
        for s in cresult:
            term = Term(self)
            term.cterm = s
            result.append(term)
        return result


    def synthInv(self, symbol, bound_vars, Grammar grammar=None):
        cdef Term term = Term(self)
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)
        if grammar is None:
            term.cterm = self.csolver.synthInv(symbol.encode(), <const vector[c_Term]&> v)
        else:
            term.cterm = self.csolver.synthInv(symbol.encode(), <const vector[c_Term]&> v, grammar.cgrammar)
        return term

    @expand_list_arg(num_req_args=0)
    def checkSatAssuming(self, *assumptions):
        '''
            Supports the following arguments:
                 Result checkSatAssuming(List[Term] assumptions)

                 where assumptions can also be comma-separated arguments of
                 type (boolean) Term
        '''
        cdef Result r = Result()
        # used if assumptions is a list of terms
        cdef vector[c_Term] v
        for a in assumptions:
            v.push_back((<Term?> a).cterm)
        r.cr = self.csolver.checkSatAssuming(<const vector[c_Term]&> v)
        return r

    @expand_list_arg(num_req_args=0)
    def checkEntailed(self, *assumptions):
        '''
            Supports the following arguments:
                 Result checkEntailed(List[Term] assumptions)

                 where assumptions can also be comma-separated arguments of
                 type (boolean) Term
        '''
        cdef Result r = Result()
        # used if assumptions is a list of terms
        cdef vector[c_Term] v
        for a in assumptions:
            v.push_back((<Term?> a).cterm)
        r.cr = self.csolver.checkEntailed(<const vector[c_Term]&> v)
        return r

    @expand_list_arg(num_req_args=1)
    def declareDatatype(self, str symbol, *ctors):
        '''
            Supports the following arguments:
                 Sort declareDatatype(str symbol, List[Term] ctors)

                 where ctors can also be comma-separated arguments of
                  type DatatypeConstructorDecl
        '''
        cdef Sort sort = Sort(self)
        cdef vector[c_DatatypeConstructorDecl] v

        for c in ctors:
            v.push_back((<DatatypeConstructorDecl?> c).cddc)
        sort.csort = self.csolver.declareDatatype(symbol.encode(), v)
        return sort

    def declareFun(self, str symbol, list sorts, Sort sort):
        cdef Term term = Term(self)
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        term.cterm = self.csolver.declareFun(symbol.encode(),
                                             <const vector[c_Sort]&> v,
                                             sort.csort)
        return term

    def declareSort(self, str symbol, int arity):
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.declareSort(symbol.encode(), arity)
        return sort

    def defineFun(self, sym_or_fun, bound_vars, sort_or_term, t=None, glbl=False):
        '''
        Supports two uses:
                Term defineFun(str symbol, List[Term] bound_vars,
                               Sort sort, Term term, bool glbl)
                Term defineFun(Term fun, List[Term] bound_vars,
                               Term term, bool glbl)
        '''
        cdef Term term = Term(self)
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)

        if t is not None:
            term.cterm = self.csolver.defineFun((<str?> sym_or_fun).encode(),
                                                <const vector[c_Term] &> v,
                                                (<Sort?> sort_or_term).csort,
                                                (<Term?> t).cterm,
                                                <bint> glbl)
        else:
            term.cterm = self.csolver.defineFun((<Term?> sym_or_fun).cterm,
                                                <const vector[c_Term]&> v,
                                                (<Term?> sort_or_term).cterm,
                                                <bint> glbl)

        return term

    def defineFunRec(self, sym_or_fun, bound_vars, sort_or_term, t=None, glbl=False):
        '''
        Supports two uses:
                Term defineFunRec(str symbol, List[Term] bound_vars,
                               Sort sort, Term term, bool glbl)
                Term defineFunRec(Term fun, List[Term] bound_vars,
                               Term term, bool glbl)
        '''
        cdef Term term = Term(self)
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)

        if t is not None:
            term.cterm = self.csolver.defineFunRec((<str?> sym_or_fun).encode(),
                                                <const vector[c_Term] &> v,
                                                (<Sort?> sort_or_term).csort,
                                                (<Term?> t).cterm,
                                                <bint> glbl)
        else:
            term.cterm = self.csolver.defineFunRec((<Term?> sym_or_fun).cterm,
                                                   <const vector[c_Term]&> v,
                                                   (<Term?> sort_or_term).cterm,
                                                   <bint> glbl)

        return term

    def defineFunsRec(self, funs, bound_vars, terms):
        cdef vector[c_Term] vf
        cdef vector[vector[c_Term]] vbv
        cdef vector[c_Term] vt

        for f in funs:
            vf.push_back((<Term?> f).cterm)

        cdef vector[c_Term] temp
        for v in bound_vars:
            for t in v:
                temp.push_back((<Term?> t).cterm)
            vbv.push_back(temp)
            temp.clear()

        for t in terms:
            vf.push_back((<Term?> t).cterm)

    def getAssertions(self):
        assertions = []
        for a in self.csolver.getAssertions():
            term = Term(self)
            term.cterm = a
            assertions.append(term)
        return assertions

    def getInfo(self, str flag):
        return self.csolver.getInfo(flag.encode())

    def getOption(self, str option):
        return self.csolver.getOption(option.encode())

    def getUnsatAssumptions(self):
        assumptions = []
        for a in self.csolver.getUnsatAssumptions():
            term = Term(self)
            term.cterm = a
            assumptions.append(term)
        return assumptions

    def getUnsatCore(self):
        core = []
        for a in self.csolver.getUnsatCore():
            term = Term(self)
            term.cterm = a
            core.append(term)
        return core

    def getValue(self, Term t):
        cdef Term term = Term(self)
        term.cterm = self.csolver.getValue(t.cterm)
        return term

    def getSeparationHeap(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.getSeparationHeap()
        return term

    def declareSeparationHeap(self, Sort locType, Sort dataType):
        self.csolver.declareSeparationHeap(locType.csort, dataType.csort)

    def getSeparationNilTerm(self):
        cdef Term term = Term(self)
        term.cterm = self.csolver.getSeparationNilTerm()
        return term

    def declarePool(self, str symbol, Sort sort, initValue):
        cdef Term term = Term(self)
        cdef vector[c_Term] niv
        for v in initValue:
            niv.push_back((<Term?> v).cterm)
        term.cterm = self.csolver.declarePool(symbol.encode(), sort.csort, niv)
        return term

    def pop(self, nscopes=1):
        self.csolver.pop(nscopes)

    def push(self, nscopes=1):
        self.csolver.push(nscopes)

    def resetAssertions(self):
        self.csolver.resetAssertions()

    def setInfo(self, str keyword, str value):
        self.csolver.setInfo(keyword.encode(), value.encode())

    def setLogic(self, str logic):
        self.csolver.setLogic(logic.encode())

    def setOption(self, str option, str value):
        self.csolver.setOption(option.encode(), value.encode())


cdef class Sort:
    cdef c_Sort csort
    cdef Solver solver
    def __cinit__(self, Solver solver):
        # csort always set by Solver
        self.solver = solver

    def __eq__(self, Sort other):
        return self.csort == other.csort

    def __ne__(self, Sort other):
        return self.csort != other.csort

    def __lt__(self, Sort other):
        return self.csort < other.csort

    def __gt__(self, Sort other):
        return self.csort > other.csort

    def __le__(self, Sort other):
        return self.csort <= other.csort

    def __ge__(self, Sort other):
        return self.csort >= other.csort

    def __str__(self):
        return self.csort.toString().decode()

    def __repr__(self):
        return self.csort.toString().decode()

    def __hash__(self):
        return csorthash(self.csort)

    def isBoolean(self):
        return self.csort.isBoolean()

    def isInteger(self):
        return self.csort.isInteger()

    def isReal(self):
        return self.csort.isReal()

    def isString(self):
        return self.csort.isString()

    def isRegExp(self):
        return self.csort.isRegExp()

    def isRoundingMode(self):
        return self.csort.isRoundingMode()

    def isBitVector(self):
        return self.csort.isBitVector()

    def isFloatingPoint(self):
        return self.csort.isFloatingPoint()

    def isDatatype(self):
        return self.csort.isDatatype()

    def isParametricDatatype(self):
        return self.csort.isParametricDatatype()

    def isConstructor(self):
        return self.csort.isConstructor()

    def isSelector(self):
        return self.csort.isSelector()

    def isTester(self):
        return self.csort.isTester()

    def isFunction(self):
        return self.csort.isFunction()

    def isPredicate(self):
        return self.csort.isPredicate()

    def isTuple(self):
        return self.csort.isTuple()

    def isRecord(self):
        return self.csort.isRecord()

    def isArray(self):
        return self.csort.isArray()

    def isSet(self):
        return self.csort.isSet()

    def isBag(self):
        return self.csort.isBag()
    
    def isSequence(self):
        return self.csort.isSequence()

    def isUninterpretedSort(self):
        return self.csort.isUninterpretedSort()

    def isSortConstructor(self):
        return self.csort.isSortConstructor()

    def isFirstClass(self):
        return self.csort.isFirstClass()

    def isFunctionLike(self):
        return self.csort.isFunctionLike()

    def isSubsortOf(self, Sort sort):
        return self.csort.isSubsortOf(sort.csort)

    def isComparableTo(self, Sort sort):
        return self.csort.isComparableTo(sort.csort)

    def getDatatype(self):
        cdef Datatype d = Datatype(self.solver)
        d.cd = self.csort.getDatatype()
        return d

    def instantiate(self, params):
        cdef Sort sort = Sort(self.solver)
        cdef vector[c_Sort] v
        for s in params:
            v.push_back((<Sort?> s).csort)
        sort.csort = self.csort.instantiate(v)
        return sort

    def getConstructorArity(self):
        return self.csort.getConstructorArity()

    def getConstructorDomainSorts(self):
        domain_sorts = []
        for s in self.csort.getConstructorDomainSorts():
            sort = Sort(self.solver)
            sort.csort = s
            domain_sorts.append(sort)
        return domain_sorts

    def getConstructorCodomainSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getConstructorCodomainSort()
        return sort

    def getSelectorDomainSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSelectorDomainSort()
        return sort

    def getSelectorCodomainSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSelectorCodomainSort()
        return sort

    def getTesterDomainSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getTesterDomainSort()
        return sort

    def getTesterCodomainSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getTesterCodomainSort()
        return sort
    
    def getFunctionArity(self):
        return self.csort.getFunctionArity()

    def getFunctionDomainSorts(self):
        domain_sorts = []
        for s in self.csort.getFunctionDomainSorts():
            sort = Sort(self.solver)
            sort.csort = s
            domain_sorts.append(sort)
        return domain_sorts

    def getFunctionCodomainSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getFunctionCodomainSort()
        return sort

    def getArrayIndexSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getArrayIndexSort()
        return sort

    def getArrayElementSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getArrayElementSort()
        return sort

    def getSetElementSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSetElementSort()
        return sort

    def getBagElementSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getBagElementSort()
        return sort

    def getSequenceElementSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSequenceElementSort()
        return sort

    def getUninterpretedSortName(self):
        return self.csort.getUninterpretedSortName().decode()

    def isUninterpretedSortParameterized(self):
        return self.csort.isUninterpretedSortParameterized()

    def getUninterpretedSortParamSorts(self):
        param_sorts = []
        for s in self.csort.getUninterpretedSortParamSorts():
            sort = Sort(self.solver)
            sort.csort = s
            param_sorts.append(sort)
        return param_sorts

    def getSortConstructorName(self):
        return self.csort.getSortConstructorName().decode()

    def getSortConstructorArity(self):
        return self.csort.getSortConstructorArity()

    def getBVSize(self):
        return self.csort.getBVSize()

    def getFPExponentSize(self):
        return self.csort.getFPExponentSize()

    def getFPSignificandSize(self):
        return self.csort.getFPSignificandSize()

    def getDatatypeParamSorts(self):
        param_sorts = []
        for s in self.csort.getDatatypeParamSorts():
            sort = Sort(self.solver)
            sort.csort = s
            param_sorts.append(sort)
        return param_sorts

    def getDatatypeArity(self):
        return self.csort.getDatatypeArity()

    def getTupleLength(self):
        return self.csort.getTupleLength()

    def getTupleSorts(self):
        tuple_sorts = []
        for s in self.csort.getTupleSorts():
            sort = Sort(self.solver)
            sort.csort = s
            tuple_sorts.append(sort)
        return tuple_sorts


cdef class Term:
    cdef c_Term cterm
    cdef Solver solver
    def __cinit__(self, Solver solver):
        # cterm always set in the Solver object
        self.solver = solver

    def __eq__(self, Term other):
        return self.cterm == other.cterm

    def __ne__(self, Term other):
        return self.cterm != other.cterm

    def __lt__(self, Term other):
        return self.cterm < other.cterm

    def __gt__(self, Term other):
        return self.cterm > other.cterm

    def __le__(self, Term other):
        return self.cterm <= other.cterm

    def __ge__(self, Term other):
        return self.cterm >= other.cterm

    def __getitem__(self, int index):
        cdef Term term = Term(self.solver)
        if index >= 0:
            term.cterm = self.cterm[index]
        else:
            raise ValueError("Expecting a non-negative integer or string")
        return term

    def __str__(self):
        return self.cterm.toString().decode()

    def __repr__(self):
        return self.cterm.toString().decode()

    def __iter__(self):
        for ci in self.cterm:
            term = Term(self.solver)
            term.cterm = ci
            yield term

    def __hash__(self):
        return ctermhash(self.cterm)

    def getNumChildren(self):
        return self.cterm.getNumChildren()

    def getId(self):
        return self.cterm.getId()

    def getKind(self):
        return kind(<int> self.cterm.getKind())

    def getSort(self):
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.cterm.getSort()
        return sort

    def substitute(self, term_or_list_1, term_or_list_2):
        # The resulting term after substitution
        cdef Term term = Term(self.solver)
        # lists for substitutions
        cdef vector[c_Term] ces
        cdef vector[c_Term] creplacements
        
        # normalize the input parameters to be lists
        if isinstance(term_or_list_1, list):
            assert isinstance(term_or_list_2, list)
            es = term_or_list_1
            replacements = term_or_list_2
            if len(es) != len(replacements):
                raise RuntimeError("Expecting list inputs to substitute to "
                                   "have the same length but got: "
                                   "{} and {}".format(len(es), len(replacements)))

            for e, r in zip(es, replacements):
                ces.push_back((<Term?> e).cterm)
                creplacements.push_back((<Term?> r).cterm)

        else:
            # add the single elements to the vectors
            ces.push_back((<Term?> term_or_list_1).cterm)
            creplacements.push_back((<Term?> term_or_list_2).cterm)
        
        # call the API substitute method with lists
        term.cterm = self.cterm.substitute(ces, creplacements)
        return term

    def hasOp(self):
        return self.cterm.hasOp()

    def getOp(self):
        cdef Op op = Op(self.solver)
        op.cop = self.cterm.getOp()
        return op

    def isNull(self):
        return self.cterm.isNull()

    def notTerm(self):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.notTerm()
        return term

    def andTerm(self, Term t):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.andTerm((<Term> t).cterm)
        return term

    def orTerm(self, Term t):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.orTerm(t.cterm)
        return term

    def xorTerm(self, Term t):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.xorTerm(t.cterm)
        return term

    def eqTerm(self, Term t):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.eqTerm(t.cterm)
        return term

    def impTerm(self, Term t):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.impTerm(t.cterm)
        return term

    def iteTerm(self, Term then_t, Term else_t):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.iteTerm(then_t.cterm, else_t.cterm)
        return term

    def isConstArray(self):
        return self.cterm.isConstArray()

    def getConstArrayBase(self):
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.getConstArrayBase()
        return term

    def isBooleanValue(self):
        return self.cterm.isBooleanValue()

    def getBooleanValue(self):
        return self.cterm.getBooleanValue()

    def isStringValue(self):
        return self.cterm.isStringValue()

    def getStringValue(self):
        cdef Py_ssize_t size
        cdef c_wstring s = self.cterm.getStringValue()
        return PyUnicode_FromWideChar(s.data(), s.size())

    def isIntegerValue(self):
        return self.cterm.isIntegerValue()
    def isAbstractValue(self):
        return self.cterm.isAbstractValue()

    def getAbstractValue(self):
        return self.cterm.getAbstractValue().decode()

    def isFloatingPointPosZero(self):
        return self.cterm.isFloatingPointPosZero()
    
    def isFloatingPointNegZero(self):
        return self.cterm.isFloatingPointNegZero()
    
    def isFloatingPointPosInf(self):
        return self.cterm.isFloatingPointPosInf()
    
    def isFloatingPointNegInf(self):
        return self.cterm.isFloatingPointNegInf()
    
    def isFloatingPointNaN(self):
        return self.cterm.isFloatingPointNaN()
    
    def isFloatingPointValue(self):
        return self.cterm.isFloatingPointValue()

    def getFloatingPointValue(self):
        cdef c_tuple[uint32_t, uint32_t, c_Term] t = self.cterm.getFloatingPointValue()
        cdef Term term = Term(self.solver)
        term.cterm = get2(t)
        return (get0(t), get1(t), term)

    def isSetValue(self):
        return self.cterm.isSetValue()

    def getSetValue(self):
        elems = set()
        for e in self.cterm.getSetValue():
            term = Term(self.solver)
            term.cterm = e
            elems.add(term)
        return elems

    def isSequenceValue(self):
        return self.cterm.isSequenceValue()

    def getSequenceValue(self):
        elems = []
        for e in self.cterm.getSequenceValue():
            term = Term(self.solver)
            term.cterm = e
            elems.append(term)
        return elems

    def isUninterpretedValue(self):
        return self.cterm.isUninterpretedValue()
 
    def getUninterpretedValue(self):
        cdef pair[c_Sort, int32_t] p = self.cterm.getUninterpretedValue()
        cdef Sort sort = Sort(self.solver)
        sort.csort = p.first
        i = p.second
        return (sort, i)

    def isTupleValue(self):
        return self.cterm.isTupleValue()

    def getTupleValue(self):
        elems = []
        for e in self.cterm.getTupleValue():
            term = Term(self.solver)
            term.cterm = e
            elems.append(term)
        return elems

    def getIntegerValue(self):
        return int(self.cterm.getIntegerValue().decode())

    def isRealValue(self):
        return self.cterm.isRealValue()

    def getRealValue(self):
        '''Returns the value of a real term as a Fraction'''
        return Fraction(self.cterm.getRealValue().decode())

    def isBitVectorValue(self):
        return self.cterm.isBitVectorValue()

    def getBitVectorValue(self, base = 2):
        '''Returns the value of a bit-vector term as a 0/1 string'''
        return self.cterm.getBitVectorValue(base).decode()

    def toPythonObj(self):
        '''
        Converts a constant value Term to a Python object.

        Currently supports:
          Boolean -- returns a Python bool
          Int     -- returns a Python int
          Real    -- returns a Python Fraction
          BV      -- returns a Python int (treats BV as unsigned)
          String  -- returns a Python Unicode string
          Array   -- returns a Python dict mapping indices to values
                  -- the constant base is returned as the default value
        '''

        if self.isBooleanValue():
            return self.getBooleanValue()
        elif self.isIntegerValue():
            return self.getIntegerValue()
        elif self.isRealValue():
            return self.getRealValue()
        elif self.isBitVectorValue():
            return int(self.getBitVectorValue(), 2)
        elif self.isStringValue():
            return self.getStringValue()
        elif self.getSort().isArray():
            res = None
            keys = []
            values = []
            base_value = None
            to_visit = [self]
            # Array models are represented as a series of store operations
            # on a constant array
            while to_visit:
                t = to_visit.pop()
                if t.getKind() == kinds.Store:
                    # save the mappings
                    keys.append(t[1].toPythonObj())
                    values.append(t[2].toPythonObj())
                    to_visit.append(t[0])
                else:
                    assert t.getKind() == kinds.ConstArray
                    base_value = t.getConstArrayBase().toPythonObj()

            assert len(keys) == len(values)
            assert base_value is not None

            # put everything in a dictionary with the constant
            # base as the result for any index not included in the stores
            res = defaultdict(lambda : base_value)
            for k, v in zip(keys, values):
                res[k] = v

            return res


# Generate rounding modes
cdef __rounding_modes = {
    <int> ROUND_NEAREST_TIES_TO_EVEN: "RoundNearestTiesToEven",
    <int> ROUND_TOWARD_POSITIVE: "RoundTowardPositive",
    <int> ROUND_TOWARD_NEGATIVE: "RoundTowardNegative",
    <int> ROUND_TOWARD_ZERO: "RoundTowardZero",
    <int> ROUND_NEAREST_TIES_TO_AWAY: "RoundNearestTiesToAway"
}

mod_ref = sys.modules[__name__]
for rm_int, name in __rounding_modes.items():
    r = RoundingMode(rm_int)

    if name in dir(mod_ref):
        raise RuntimeError("Redefinition of Python RoundingMode %s."%name)

    setattr(mod_ref, name, r)

del r
del rm_int
del name
