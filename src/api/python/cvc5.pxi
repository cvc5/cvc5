from collections import defaultdict
from fractions import Fraction
from functools import wraps
import sys

from cython.operator cimport dereference, preincrement

from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libc.stddef cimport wchar_t

from libcpp cimport bool as c_bool
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
from cvc5 cimport SynthResult as c_SynthResult
from cvc5 cimport Op as c_Op
from cvc5 cimport OptionInfo as c_OptionInfo
from cvc5 cimport holds as c_holds
from cvc5 cimport getVariant as c_getVariant
from cvc5 cimport Solver as c_Solver
from cvc5 cimport Statistics as c_Statistics
from cvc5 cimport Stat as c_Stat
from cvc5 cimport Grammar as c_Grammar
from cvc5 cimport Sort as c_Sort
from cvc5 cimport Term as c_Term
from cvc5 cimport hash as c_hash
from cvc5 cimport wstring as c_wstring
from cvc5 cimport tuple as c_tuple
from cvc5 cimport get0, get1, get2
from cvc5kinds cimport Kind as c_Kind
from cvc5types cimport RoundingMode as c_RoundingMode
from cvc5types cimport UnknownExplanation as c_UnknownExplanation

cdef extern from "Python.h":
    wchar_t* PyUnicode_AsWideCharString(object, Py_ssize_t *)
    object PyUnicode_FromWideChar(const wchar_t*, Py_ssize_t)
    void PyMem_Free(void*)

################################## DECORATORS #################################
def expand_list_arg(num_req_args=0):
    """
    Creates a decorator that looks at index num_req_args of the args,
    if it's a list, it expands it before calling the function.
    """
    def decorator(func):
        @wraps(func)
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
    """
        A cvc5 datatype.
        Wrapper class for :cpp:class:`cvc5::Datatype`.
    """
    cdef c_Datatype cd
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.solver = solver

    def __getitem__(self, index):
        cdef DatatypeConstructor dc = DatatypeConstructor(self.solver)
        if isinstance(index, int) and index >= 0:
            dc.cdc = self.cd[(<int?> index)]
        elif isinstance(index, str):
            dc.cdc = self.cd[(<const string &> index.encode())]
        else:
            raise ValueError("Expecting a non-negative integer or string")
        return dc

    def getConstructor(self, str name):
        """
            :param name: the name of the constructor.
            :return: a constructor by name.
        """
        cdef DatatypeConstructor dc = DatatypeConstructor(self.solver)
        dc.cdc = self.cd.getConstructor(name.encode())
        return dc

    def getConstructorTerm(self, str name):
        """
            :param name: the name of the constructor.
            :return: the term representing the datatype constructor with the given name (see :cpp:func:`Datatype::getConstructorTerm() <cvc5::Datatype::getConstructorTerm>`).
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cd.getConstructorTerm(name.encode())
        return term

    def getSelector(self, str name):
        """
            :param name: the name of the selector..
            :return: a selector by name.
        """
        cdef DatatypeSelector ds = DatatypeSelector(self.solver)
        ds.cds = self.cd.getSelector(name.encode())
        return ds

    def getName(self):
        """
            :return: the name of the datatype.
        """
        return self.cd.getName().decode()

    def getNumConstructors(self):
        """
            :return: number of constructors in this datatype.
        """
        return self.cd.getNumConstructors()

    def getParameters(self):
        """
            :return: the parameters of this datatype, if it is parametric. An exception is thrown if this datatype is not parametric.
        """
        param_sorts = []
        for s in self.cd.getParameters():
            sort = Sort(self.solver)
            sort.csort = s
            param_sorts.append(sort)
        return param_sorts

    def isParametric(self):
        """
            .. warning:: This method is experimental and may change in future
                         versions.
            :return: True if this datatype is parametric.
        """
        return self.cd.isParametric()

    def isCodatatype(self):
        """:return: True if this datatype corresponds to a co-datatype."""
        return self.cd.isCodatatype()

    def isTuple(self):
        """:return: True if this datatype corresponds to a tuple."""
        return self.cd.isTuple()

    def isRecord(self):
        """
            .. warning:: This method is experimental and may change in future
                         versions.
            :return: True if this datatype corresponds to a record.
        """
        return self.cd.isRecord()

    def isFinite(self):
        """:return: True if this datatype is finite."""
        return self.cd.isFinite()

    def isWellFounded(self):
        """:return: True if this datatype is well-founded (see :cpp:func:`Datatype::isWellFounded() <cvc5::Datatype::isWellFounded>`)."""
        return self.cd.isWellFounded()

    def isNull(self):
        """:return: True if this Datatype is a null object."""
        return self.cd.isNull()

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
    """
        A cvc5 datatype constructor.
        Wrapper class for :cpp:class:`cvc5::DatatypeConstructor`.
    """
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
        """
            :return: the name of the constructor.
        """
        return self.cdc.getName().decode()

    def getConstructorTerm(self):
        """
            :return: the constructor operator as a term.
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getConstructorTerm()
        return term

    def getInstantiatedConstructorTerm(self, Sort retSort):
        """
            Specialized method for parametric datatypes (see
            :cpp:func:`DatatypeConstructor::getInstantiatedConstructorTerm()
            <cvc5::DatatypeConstructor::getInstantiatedConstructorTerm>`).

            .. warning:: This method is experimental and may change in future
                         versions.

            :param retSort: the desired return sort of the constructor
            :return: the constructor operator as a term.
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getInstantiatedConstructorTerm(retSort.csort)
        return term

    def getTesterTerm(self):
        """
            :return: the tester operator that is related to this constructor, as a term.
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getTesterTerm()
        return term

    def getNumSelectors(self):
        """
            :return: the number of selecters (so far) of this Datatype constructor.
        """
        return self.cdc.getNumSelectors()

    def getSelector(self, str name):
        """
            :param name: the name of the datatype selector.
            :return: the first datatype selector with the given name
        """
        cdef DatatypeSelector ds = DatatypeSelector(self.solver)
        ds.cds = self.cdc.getSelector(name.encode())
        return ds

    def getSelectorTerm(self, str name):
        """
            :param name: the name of the datatype selector.
            :return: a term representing the firstdatatype selector with the given name.
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cdc.getSelectorTerm(name.encode())
        return term

    def isNull(self):
        """:return: True if this DatatypeConstructor is a null object."""
        return self.cdc.isNull()

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
    """
        A cvc5 datatype constructor declaration.
        Wrapper class for :cpp:class:`cvc5::DatatypeConstructorDecl`.
    """
    cdef c_DatatypeConstructorDecl cddc
    cdef Solver solver

    def __cinit__(self, Solver solver):
        self.solver = solver

    def addSelector(self, str name, Sort sort):
        """
            Add datatype selector declaration.

            :param name: the name of the datatype selector declaration to add.
            :param sort: the codomain sort of the datatype selector declaration
                         to add.
        """
        self.cddc.addSelector(name.encode(), sort.csort)

    def addSelectorSelf(self, str name):
        """
            Add datatype selector declaration whose codomain sort is the
            datatype itself.

            :param name: the name of the datatype selector declaration to add.
        """
        self.cddc.addSelectorSelf(name.encode())

    def isNull(self):
        """:return: True if this DatatypeConstructorDecl is a null object."""
        return self.cddc.isNull()

    def __str__(self):
        return self.cddc.toString().decode()

    def __repr__(self):
        return self.cddc.toString().decode()


cdef class DatatypeDecl:
    """
        A cvc5 datatype declaration.
        Wrapper class for :cpp:class:`cvc5::DatatypeDecl`.
    """
    cdef c_DatatypeDecl cdd
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.solver = solver

    def addConstructor(self, DatatypeConstructorDecl ctor):
        """
            Add a datatype constructor declaration.

            :param ctor: the datatype constructor declaration to add.
        """
        self.cdd.addConstructor(ctor.cddc)

    def getNumConstructors(self):
        """
            :return: number of constructors (so far) for this datatype declaration.
        """
        return self.cdd.getNumConstructors()

    def isParametric(self):
        """
            :return: is this datatype declaration parametric?
        """
        return self.cdd.isParametric()

    def getName(self):
        """
            :return: the name of this datatype declaration.
        """
        return self.cdd.getName().decode()

    def isNull(self):
        """:return: True if this DatatypeDecl is a null object."""
        return self.cdd.isNull()

    def __str__(self):
        return self.cdd.toString().decode()

    def __repr__(self):
        return self.cdd.toString().decode()


cdef class DatatypeSelector:
    """
        A cvc5 datatype selector.
        Wrapper class for :cpp:class:`cvc5::DatatypeSelector`.
    """
    cdef c_DatatypeSelector cds
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.cds = c_DatatypeSelector()
        self.solver = solver

    def getName(self):
        """
            :return: the name of this datatype selector.
        """
        return self.cds.getName().decode()

    def getSelectorTerm(self):
        """
            :return: the selector opeartor of this datatype selector as a term.
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cds.getSelectorTerm()
        return term

    def getUpdaterTerm(self):
        """
            :return: the updater opeartor of this datatype selector as a term.
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cds.getUpdaterTerm()
        return term

    def getCodomainSort(self):
        """
            :return: the codomain sort of this selector.
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.cds.getCodomainSort()
        return sort

    def isNull(self):
        """:return: True if this DatatypeSelector is a null object."""
        return self.cds.isNull()

    def __str__(self):
        return self.cds.toString().decode()

    def __repr__(self):
        return self.cds.toString().decode()


cdef class Op:
    """
        A cvc5 operator.
        An operator is a term that represents certain operators,
        instantiated with its required parameters, e.g.,
        a term of kind :cpp:enumerator:`BITVECTOR_EXTRACT`.
        Wrapper class for :cpp:class:`cvc5::Op`.
    """
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
        """
            :return: the kind of this operator.
        """
        return Kind(<int> self.cop.getKind())

    def isIndexed(self):
        """
            :return: True iff this operator is indexed.
        """
        return self.cop.isIndexed()

    def isNull(self):
        """
            :return: True iff this operator is a null term.
        """
        return self.cop.isNull()

    def getNumIndices(self):
        """
            :return: number of indices of this op.
        """
        return self.cop.getNumIndices()

    def __getitem__(self, i):
        """
            Get the index at position i.
            :param i: the position of the index to return
            :return: the index at position i
        """
        cdef Term term = Term(self.solver)
        term.cterm = self.cop[i]
        return term


cdef class Grammar:
    """
        A Sygus Grammar.
        Wrapper class for :cpp:class:`cvc5::Grammar`.
    """
    cdef c_Grammar  cgrammar
    cdef Solver solver
    def __cinit__(self, Solver solver):
        self.solver = solver
        self.cgrammar = c_Grammar()

    def addRule(self, Term ntSymbol, Term rule):
        """
            Add ``rule`` to the set of rules corresponding to ``ntSymbol``.

            :param ntSymbol: the non-terminal to which the rule is added.
            :param rule: the rule to add.
        """
        self.cgrammar.addRule(ntSymbol.cterm, rule.cterm)

    def addAnyConstant(self, Term ntSymbol):
        """
            Allow ``ntSymbol`` to be an arbitrary constant.

            :param ntSymbol: the non-terminal allowed to be constant.
        """
        self.cgrammar.addAnyConstant(ntSymbol.cterm)

    def addAnyVariable(self, Term ntSymbol):
        """
            Allow ``ntSymbol`` to be any input variable to corresponding synth-fun/synth-inv with the same sort as ``ntSymbol``.

            :param ntSymbol: the non-terminal allowed to be any input variable.
        """
        self.cgrammar.addAnyVariable(ntSymbol.cterm)

    def addRules(self, Term ntSymbol, rules):
        """
            Add ``ntSymbol`` to the set of rules corresponding to ``ntSymbol``.

            :param ntSymbol: the non-terminal to which the rules are added.
            :param rules: the rules to add.
        """
        cdef vector[c_Term] crules
        for r in rules:
            crules.push_back((<Term?> r).cterm)
        self.cgrammar.addRules(ntSymbol.cterm, crules)

cdef class Result:
    """
        Encapsulation of a three-valued solver result, with explanations.
        Wrapper class for :cpp:class:`cvc5::Result`.
    """
    cdef c_Result cr
    def __cinit__(self):
        # gets populated by solver
        self.cr = c_Result()

    def isNull(self):
        """
            :return: True if Result is empty, i.e., a nullary Result, and not an actual result returned from a
                     :cpp:func:`Solver::checkSat() <cvc5::Solver::checkSat>` (and friends) query.
        """
        return self.cr.isNull()

    def isSat(self):
        """
            :return: True if query was a satisfiable :cpp:func:`Solver::checkSat() <cvc5::Solver::checkSat>` or :cpp:func:`Solver::checkSatAssuming() <cvc5::Solver::checkSatAssuming>` query.
        """
        return self.cr.isSat()

    def isUnsat(self):
        """
            :return: True if query was an usatisfiable :cpp:func:`Solver::checkSat() <cvc5::Solver::checkSat>` or :cpp:func:`Solver::checkSatAssuming() <cvc5::Solver::checkSatAssuming>` query.
        """
        return self.cr.isUnsat()

    def isUnknown(self):
        """
            :return: True if query was a :cpp:func:`Solver::checkSat() <cvc5::Solver::checkSat>` or :cpp:func:`Solver::checkSatAssuming() <cvc5::Solver::checkSatAssuming>` query and cvc5 was not able to determine (un)satisfiability.
        """
        return self.cr.isUnknown()

    def getUnknownExplanation(self):
        """
            :return: an explanation for an unknown query result.
        """
        return UnknownExplanation(<int> self.cr.getUnknownExplanation())

    def __eq__(self, Result other):
        return self.cr == other.cr

    def __ne__(self, Result other):
        return self.cr != other.cr

    def __str__(self):
        return self.cr.toString().decode()

    def __repr__(self):
        return self.cr.toString().decode()

cdef class SynthResult:
    """
      Encapsulation of a solver synth result. This is the return value of the
      API methods:
        - :py:meth:`Solver.checkSynth()`
        - :py:meth:`Solver.checkSynthNext()`
      which we call synthesis queries. This class indicates whether the
      synthesis query has a solution, has no solution, or is unknown.
    """
    cdef c_SynthResult cr
    def __cinit__(self):
        # gets populated by solver
        self.cr = c_SynthResult()

    def isNull(self):
        """
            :return: True if SynthResult is null, i.e. not a SynthResult returned from a synthesis query.
        """
        return self.cr.isNull()

    def hasSolution(self):
        """
            :return: True if the synthesis query has a solution.
        """
        return self.cr.hasSolution()

    def hasNoSolution(self):
        """
            :return: True if the synthesis query has no solution.
            In this case, then it was determined there was no solution.
        """
        return self.cr.hasNoSolution()

    def isUnknown(self):
        """
            :return: True if the result of the synthesis query could not be determined.
        """
        return self.cr.isUnknown()

    def __str__(self):
        return self.cr.toString().decode()

    def __repr__(self):
        return self.cr.toString().decode()


cdef class Solver:
    """Wrapper class for :cpp:class:`cvc5::Solver`."""
    cdef c_Solver* csolver

    def __cinit__(self):
        self.csolver = new c_Solver()

    def __dealloc__(self):
        del self.csolver

    def getBooleanSort(self):
        """:return: sort Boolean
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getBooleanSort()
        return sort

    def getIntegerSort(self):
        """:return: sort Integer
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getIntegerSort()
        return sort

    def getNullSort(self):
        """:return: sort null
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getNullSort()
        return sort

    def getRealSort(self):
        """:return: sort Real
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getRealSort()
        return sort

    def getRegExpSort(self):
        """:return: sort of RegExp
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getRegExpSort()
        return sort

    def getRoundingModeSort(self):
        """:return: sort RoundingMode
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getRoundingModeSort()
        return sort

    def getStringSort(self):
        """:return: sort String
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.getStringSort()
        return sort

    def mkArraySort(self, Sort indexSort, Sort elemSort):
        """Create an array sort.

        :param indexSort: the array index sort
        :param elemSort: the array element sort
        :return: the array sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkArraySort(indexSort.csort, elemSort.csort)
        return sort

    def mkBitVectorSort(self, uint32_t size):
        """Create a bit-vector sort.

        :param size: the bit-width of the bit-vector sort
        :return: the bit-vector sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkBitVectorSort(size)
        return sort

    def mkFloatingPointSort(self, uint32_t exp, uint32_t sig):
        """Create a floating-point sort.

        :param exp: the bit-width of the exponent of the floating-point sort.
        :param sig: the bit-width of the significand of the floating-point sort.
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkFloatingPointSort(exp, sig)
        return sort

    def mkDatatypeSort(self, DatatypeDecl dtypedecl):
        """Create a datatype sort.

        :param dtypedecl: the datatype declaration from which the sort is created
        :return: the datatype sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkDatatypeSort(dtypedecl.cdd)
        return sort

    def mkDatatypeSorts(self, list dtypedecls, unresolvedSorts = None):
        """
        Create a vector of datatype sorts using unresolved sorts. The names of
        the datatype declarations in dtypedecls must be distinct.

        This method is called when the DatatypeDecl objects dtypedecls have been
        built using "unresolved" sorts.

        We associate each sort in unresolvedSorts with exacly one datatype from
        dtypedecls. In particular, it must have the same name as exactly one
        datatype declaration in dtypedecls.

        When constructing datatypes, unresolved sorts are replaced by the datatype
        sort constructed for the datatype declaration it is associated with.

        :param dtypedecls: the datatype declarations from which the sort is created
        :param unresolvedSorts: the list of unresolved sorts
        :return: the datatype sorts
        """
        if unresolvedSorts == None:
            unresolvedSorts = set([])
        else:
            assert isinstance(unresolvedSorts, set)

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
        """ Create function sort.

        :param sorts: the sort of the function arguments
        :param codomain: the sort of the function return value
        :return: the function sort
        """

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
        """ Create a sort parameter.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param symbol: the name of the sort
        :return: the sort parameter
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkParamSort(symbolname.encode())
        return sort

    @expand_list_arg(num_req_args=0)
    def mkPredicateSort(self, *sorts):
        """Create a predicate sort.

        :param sorts: the list of sorts of the predicate, as a list or as distinct arguments.
        :return: the predicate sort
        """
        cdef Sort sort = Sort(self)
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        sort.csort = self.csolver.mkPredicateSort(<const vector[c_Sort]&> v)
        return sort

    @expand_list_arg(num_req_args=0)
    def mkRecordSort(self, *fields):
        """Create a record sort

        .. warning:: This method is experimental and may change in future
                     versions.

        :param fields: the list of fields of the record, as a list or as distinct arguments
        :return: the record sort
        """
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
        """Create a set sort.

        :param elemSort: the sort of the set elements
        :return: the set sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkSetSort(elemSort.csort)
        return sort

    def mkBagSort(self, Sort elemSort):
        """Create a bag sort.

        :param elemSort: the sort of the bag elements
        :return: the bag sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkBagSort(elemSort.csort)
        return sort

    def mkSequenceSort(self, Sort elemSort):
        """Create a sequence sort.

        :param elemSort: the sort of the sequence elements
        :return: the sequence sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkSequenceSort(elemSort.csort)
        return sort

    def mkUninterpretedSort(self, str name):
        """Create an uninterpreted sort.

        :param symbol: the name of the sort
        :return: the uninterpreted sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkUninterpretedSort(name.encode())
        return sort

    def mkUnresolvedSort(self, str name, size_t arity = 0):
        """Create an unresolved sort.

        This is for creating yet unresolved sort placeholders for mutually
        recursive datatypes.

        :param symbol: the name of the sort
        :param arity: the number of sort parameters of the sort
        :return: the unresolved sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkUnresolvedSort(name.encode(), arity)
        return sort

    def mkUninterpretedSortConstructorSort(self, str symbol, size_t arity):
        """Create a sort constructor sort.

        An uninterpreted sort constructor is an uninterpreted sort with
        arity > 0.

        :param symbol: the symbol of the sort
        :param arity: the arity of the sort (must be > 0)
        :return: the sort constructor sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.mkUninterpretedSortConstructorSort(
            symbol.encode(), arity)
        return sort

    @expand_list_arg(num_req_args=0)
    def mkTupleSort(self, *sorts):
        """Create a tuple sort.

        :param sorts: of the elements of the tuple, as a list or as distinct arguments
        :return: the tuple sort
        """
        cdef Sort sort = Sort(self)
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        sort.csort = self.csolver.mkTupleSort(v)
        return sort

    @expand_list_arg(num_req_args=1)
    def mkTerm(self, kind_or_op, *args):
        """
        Supports the following arguments:

        - ``Term mkTerm(Kind kind)``
        - ``Term mkTerm(Kind kind, Op child1, List[Term] children)``
        - ``Term mkTerm(Kind kind, List[Term] children)``

        where ``List[Term]`` can also be comma-separated arguments
        """
        cdef Term term = Term(self)
        cdef vector[c_Term] v

        op = kind_or_op
        if isinstance(kind_or_op, Kind):
            op = self.mkOp(kind_or_op)

        if len(args) == 0:
            term.cterm = self.csolver.mkTerm((<Op?> op).cop)
        else:
            for a in args:
                v.push_back((<Term?> a).cterm)
            term.cterm = self.csolver.mkTerm((<Op?> op).cop, v)
        return term

    def mkTuple(self, sorts, terms):
        """Create a tuple term. Terms are automatically converted if sorts are compatible.

        :param sorts: The sorts of the elements in the tuple
        :param terms: The elements in the tuple
        :return: the tuple Term
        """
        cdef vector[c_Sort] csorts
        cdef vector[c_Term] cterms

        for s in sorts:
            csorts.push_back((<Sort?> s).csort)
        for s in terms:
            cterms.push_back((<Term?> s).cterm)
        cdef Term result = Term(self)
        result.cterm = self.csolver.mkTuple(csorts, cterms)
        return result

    @expand_list_arg(num_req_args=0)
    def mkOp(self, k, *args):
        """
        Supports the following uses:

        - ``Op mkOp(Kind kind)``
        - ``Op mkOp(Kind kind, const string& arg)``
        - ``Op mkOp(Kind kind, uint32_t arg0, ...)``
        """
        cdef Op op = Op(self)
        cdef vector[uint32_t] v

        if len(args) == 0:
            op.cop = self.csolver.mkOp(<c_Kind> k.value)
        elif len(args) == 1 and isinstance(args[0], str):
            op.cop = self.csolver.mkOp(<c_Kind> k.value,
                                       <const string &>
                                       args[0].encode())
        else:
            for a in args:
                if not isinstance(a, int):
                  raise ValueError(
                            "Expected uint32_t for argument {}".format(a))
                if a < 0 or a >= 2 ** 31:
                    raise ValueError(
                            "Argument {} must fit in a uint32_t".format(a))
                v.push_back((<uint32_t?> a))
            op.cop = self.csolver.mkOp(<c_Kind> k.value, v)
        return op

    def mkTrue(self):
        """Create a Boolean true constant.

        :return: the true constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkTrue()
        return term

    def mkFalse(self):
        """Create a Boolean false constant.

        :return: the false constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFalse()
        return term

    def mkBoolean(self, bint val):
        """Create a Boolean constant.

        :return: the Boolean constant
        :param val: the value of the constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkBoolean(val)
        return term

    def mkPi(self):
        """Create a constant representing the number Pi.

        :return: a constant representing Pi
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkPi()
        return term

    def mkInteger(self, val):
        """Create an integer constant.

        :param val: representation of the constant: either a string or integer
        :return: a constant of sort Integer
        """
        cdef Term term = Term(self)
        if isinstance(val, str):
            term.cterm = self.csolver.mkInteger(<const string &> str(val).encode())
        else:
            assert(isinstance(val, int))
            term.cterm = self.csolver.mkInteger((<int?> val))
        return term

    def mkReal(self, val, den=None):
        """Create a real constant.

        :param val: the value of the term. Can be an integer, float, or string. It will be formatted as a string before the term is built.
        :param den: if not None, the value is `val`/`den`
        :return: a real term with literal value

        Can be used in various forms:

        - Given a string ``"N/D"`` constructs the corresponding rational.
        - Given a string ``"W.D"`` constructs the reduction of ``(W * P + D)/P``, where ``P`` is the appropriate power of 10.
        - Given a float ``f``, constructs the rational matching ``f``'s string representation. This means that ``mkReal(0.3)`` gives ``3/10`` and not the IEEE-754 approximation of ``3/10``.
        - Given a string ``"W"`` or an integer, constructs that integer.
        - Given two strings and/or integers ``N`` and ``D``, constructs ``N/D``.
        """
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

    def mkRegexpAll(self):
        """Create a regular expression all (re.all) term.

        :return: the all term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRegexpAll()
        return term

    def mkRegexpAllchar(self):
        """Create a regular expression allchar (re.allchar) term.

        :return: the allchar term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRegexpAllchar()
        return term

    def mkRegexpNone(self):
        """Create a regular expression none (re.none) term.

        :return: the none term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRegexpNone()
        return term

    def mkEmptySet(self, Sort s):
        """Create a constant representing an empty set of the given sort.

        :param sort: the sort of the set elements.
        :return: the empty set constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkEmptySet(s.csort)
        return term

    def mkEmptyBag(self, Sort s):
        """Create a constant representing an empty bag of the given sort.

        :param sort: the sort of the bag elements.
        :return: the empty bag constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkEmptyBag(s.csort)
        return term

    def mkSepEmp(self):
        """Create a separation logic empty term.

        .. warning:: This method is experimental and may change in future
                     versions.

        :return: the separation logic empty term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkSepEmp()
        return term

    def mkSepNil(self, Sort sort):
        """Create a separation logic nil term.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param sort: the sort of the nil term
        :return: the separation logic nil term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkSepNil(sort.csort)
        return term

    def mkString(self, str s, useEscSequences = None):
        """
        Create a String constant from a `str` which may contain SMT-LIB
        compatible escape sequences like ``\\u1234`` to encode unicode characters.

        :param s: the string this constant represents
        :param useEscSequences: determines whether escape sequences in `s` should be converted to the corresponding unicode character
        :return: the String constant
        """
        cdef Term term = Term(self)
        cdef Py_ssize_t size
        cdef wchar_t* tmp = PyUnicode_AsWideCharString(s, &size)
        if isinstance(useEscSequences, bool):
            term.cterm = self.csolver.mkString(
                s.encode(), <bint> useEscSequences)
        else:
            term.cterm = self.csolver.mkString(c_wstring(tmp, size))
        PyMem_Free(tmp)
        return term

    def mkEmptySequence(self, Sort sort):
        """Create an empty sequence of the given element sort.

        :param sort: The element sort of the sequence.
        :return: the empty sequence with given element sort.
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkEmptySequence(sort.csort)
        return term

    def mkUniverseSet(self, Sort sort):
        """Create a universe set of the given sort.

        :param sort: the sort of the set elements
        :return: the universe set constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkUniverseSet(sort.csort)
        return term

    @expand_list_arg(num_req_args=0)
    def mkBitVector(self, *args):
        """
        Supports the following arguments:

        - ``Term mkBitVector(int size, int val=0)``
        - ``Term mkBitVector(int size, string val, int base)``

        :return: a bit-vector literal term
        :param size: an integer size.
        :param val: an integer representating the value, in the first form. In the second form, a string representing the value.
        :param base: the base of the string representation (second form only)
        """
        cdef Term term = Term(self)
        if len(args) == 0:
            raise ValueError("Missing arguments to mkBitVector")
        size = args[0]
        if not isinstance(size, int):
            raise ValueError(
                "Invalid first argument to mkBitVector '{}', "
                "expected bit-vector size".format(size))
        if len(args) == 1:
            term.cterm = self.csolver.mkBitVector(<uint32_t> size)
        elif len(args) == 2:
            val = args[1]
            if not isinstance(val, int):
                raise ValueError(
                    "Invalid second argument to mkBitVector '{}', "
                    "expected integer value".format(size))
            term.cterm = self.csolver.mkBitVector(
                <uint32_t> size, <uint32_t> val)
        elif len(args) == 3:
            val = args[1]
            base = args[2]
            if not isinstance(val, str):
                raise ValueError(
                    "Invalid second argument to mkBitVector '{}', "
                    "expected value string".format(size))
            if not isinstance(base, int):
                raise ValueError(
                    "Invalid third argument to mkBitVector '{}', "
                    "expected base given as integer".format(size))
            term.cterm = self.csolver.mkBitVector(
                <uint32_t> size,
                <const string&> str(val).encode(),
                <uint32_t> base)
        else:
            raise ValueError("Unexpected inputs to mkBitVector")
        return term

    def mkConstArray(self, Sort sort, Term val):
        """
        Create a constant array with the provided constant value stored at every
        index

        :param sort: the sort of the constant array (must be an array sort)
        :param val: the constant value to store (must match the sort's element sort)
        :return: the constant array term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkConstArray(sort.csort, val.cterm)
        return term

    def mkFloatingPointPosInf(self, int exp, int sig):
        """Create a positive infinity floating-point constant.

        :param exp: Number of bits in the exponent
        :param sig: Number of bits in the significand
        :return: the floating-point constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPointPosInf(exp, sig)
        return term

    def mkFloatingPointNegInf(self, int exp, int sig):
        """Create a negative infinity floating-point constant.

        :param exp: Number of bits in the exponent
        :param sig: Number of bits in the significand
        :return: the floating-point constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPointNegInf(exp, sig)
        return term

    def mkFloatingPointNaN(self, int exp, int sig):
        """Create a not-a-number (NaN) floating-point constant.

        :param exp: Number of bits in the exponent
        :param sig: Number of bits in the significand
        :return: the floating-point constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPointNaN(exp, sig)
        return term

    def mkFloatingPointPosZero(self, int exp, int sig):
        """Create a positive zero (+0.0) floating-point constant.

        :param exp: Number of bits in the exponent
        :param sig: Number of bits in the significand
        :return: the floating-point constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPointPosZero(exp, sig)
        return term

    def mkFloatingPointNegZero(self, int exp, int sig):
        """Create a negative zero (+0.0) floating-point constant.

        :param exp: Number of bits in the exponent
        :param sig: Number of bits in the significand
        :return: the floating-point constant
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPointNegZero(exp, sig)
        return term

    def mkRoundingMode(self, rm):
        """Create a roundingmode constant.

        :param rm: the floating point rounding mode this constant represents
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkRoundingMode(<c_RoundingMode> rm.value)
        return term

    def mkFloatingPoint(self, int exp, int sig, Term val):
        """Create a floating-point constant.

        :param exp: Size of the exponent
        :param sig: Size of the significand
        :param val: Value of the floating-point constant as a bit-vector term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkFloatingPoint(exp, sig, val.cterm)
        return term

    def mkCardinalityConstraint(self, Sort sort, int index):
        """Create cardinality constraint.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param sort: Sort of the constraint
        :param index: The upper bound for the cardinality of the sort
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.mkCardinalityConstraint(sort.csort, index)
        return term

    def mkConst(self, Sort sort, symbol=None):
        """
        Create (first-order) constant (0-arity function symbol).

        SMT-LIB:

        .. code-block:: smtlib

            ( declare-const <symbol> <sort> )
            ( declare-fun <symbol> ( ) <sort> )

        :param sort: the sort of the constant
        :param symbol: the name of the constant. If None, a default symbol is used.
        :return: the first-order constant
        """
        cdef Term term = Term(self)
        if symbol is None:
            term.cterm = self.csolver.mkConst(sort.csort)
        else:
            term.cterm = self.csolver.mkConst(sort.csort,
                                            (<str?> symbol).encode())
        return term

    def mkVar(self, Sort sort, symbol=None):
        """
        Create a bound variable to be used in a binder (i.e. a quantifier, a
        lambda, or a witness binder).

        :param sort: the sort of the variable
        :param symbol: the name of the variable
        :return: the variable
        """
        cdef Term term = Term(self)
        if symbol is None:
            term.cterm = self.csolver.mkVar(sort.csort)
        else:
            term.cterm = self.csolver.mkVar(sort.csort,
                                            (<str?> symbol).encode())
        return term

    def mkDatatypeConstructorDecl(self, str name):
        """
        :param name: the constructor's name
        :return: the DatatypeConstructorDecl
        """
        cdef DatatypeConstructorDecl ddc = DatatypeConstructorDecl(self)
        ddc.cddc = self.csolver.mkDatatypeConstructorDecl(name.encode())
        return ddc

    def mkDatatypeDecl(self, str name, sorts_or_bool=None, isCoDatatype=None):
        """Create a datatype declaration.

        :param name: the name of the datatype
        :param isCoDatatype: true if a codatatype is to be constructed
        :return: the DatatypeDecl
        """
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
        """
        Simplify a formula without doing "much" work.  Does not involve the
        SAT Engine in the simplification, but uses the current definitions,
        assertions, and the current partial model, if one has been constructed.
        It also involves theory normalization.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param t: the formula to simplify
        :return: the simplified formula
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.simplify(t.cterm)
        return term

    def assertFormula(self, Term term):
        """ Assert a formula

        SMT-LIB:

        .. code-block:: smtlib

            ( assert <term> )

        :param term: the formula to assert
        """
        self.csolver.assertFormula(term.cterm)

    def checkSat(self):
        """
        Check satisfiability.

        SMT-LIB:

        .. code-block:: smtlib

            ( check-sat )

        :return: the result of the satisfiability check.
        """
        cdef Result r = Result()
        r.cr = self.csolver.checkSat()
        return r

    def mkSygusGrammar(self, boundVars, ntSymbols):
        """
        Create a SyGuS grammar. The first non-terminal is treated as the
        starting non-terminal, so the order of non-terminals matters.

        :param boundVars: the parameters to corresponding synth-fun/synth-inv
        :param ntSymbols: the pre-declaration of the non-terminal symbols
        :return: the grammar
        """
        cdef Grammar grammar = Grammar(self)
        cdef vector[c_Term] bvc
        cdef vector[c_Term] ntc
        for bv in boundVars:
            bvc.push_back((<Term?> bv).cterm)
        for nt in ntSymbols:
            ntc.push_back((<Term?> nt).cterm)
        grammar.cgrammar = self.csolver.mkSygusGrammar(<const vector[c_Term]&> bvc, <const vector[c_Term]&> ntc)
        return grammar

    def declareSygusVar(self, Sort sort, str symbol=""):
        """Append symbol to the current list of universal variables.

        SyGuS v2:

        .. code-block:: smtlib

            ( declare-var <symbol> <sort> )

        :param sort: the sort of the universal variable
        :param symbol: the name of the universal variable
        :return: the universal variable
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.declareSygusVar(sort.csort, symbol.encode())
        return term

    def addSygusConstraint(self, Term t):
        """
        Add a formula to the set of SyGuS constraints.

        SyGuS v2:

        .. code-block:: smtlib

            ( constraint <term> )

        :param term: the formula to add as a constraint
        """
        self.csolver.addSygusConstraint(t.cterm)

    def addSygusAssume(self, Term t):
        """
        Add a formula to the set of Sygus assumptions.

        SyGuS v2:

        .. code-block:: smtlib

            ( assume <term> )

        :param term: the formuula to add as an assumption
        """
        self.csolver.addSygusAssume(t.cterm)

    def addSygusInvConstraint(self, Term inv_f, Term pre_f, Term trans_f, Term post_f):
        """
        Add a set of SyGuS constraints to the current state that correspond to an
        invariant synthesis problem.

        SyGuS v2:

        .. code-block:: smtlib

            ( inv-constraint <inv> <pre> <trans> <post> )

        :param inv: the function-to-synthesize
        :param pre: the pre-condition
        :param trans: the transition relation
        :param post: the post-condition
        """
        self.csolver.addSygusInvConstraint(inv_f.cterm, pre_f.cterm, trans_f.cterm, post_f.cterm)

    def synthFun(self, str symbol, bound_vars, Sort sort, Grammar grammar=None):
        """
        Synthesize n-ary function following specified syntactic constraints.

        SyGuS v2:

        .. code-block:: smtlib

            ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )

        :param symbol: the name of the function
        :param boundVars: the parameters to this function
        :param sort: the sort of the return value of this function
        :param grammar: the syntactic constraints
        :return: the function
        """
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
        """
        Try to find a solution for the synthesis conjecture corresponding to the
        current list of functions-to-synthesize, universal variables and
        constraints.

        SyGuS v2:

        .. code-block:: smtlib

            ( check-synth )

        :return: the result of the check, which is "solution" if the check
                 found a solution in which case solutions are available via
                 getSynthSolutions, "no solution" if it was determined there is
                 no solution, or "unknown" otherwise.
        """
        cdef SynthResult r = SynthResult()
        r.cr = self.csolver.checkSynth()
        return r

    def checkSynthNext(self):
        """
        Try to find a next solution for the synthesis conjecture corresponding
        to the current list of functions-to-synthesize, universal variables and
        constraints. Must be called immediately after a successful call to
        check-synth or check-synth-next. Requires incremental mode.

        SyGuS v2:

        .. code-block:: smtlib

            ( check-synth )

        :return: the result of the check, which is "solution" if the check
                 found a solution in which case solutions are available via
                 getSynthSolutions, "no solution" if it was determined there is
                 no solution, or "unknown" otherwise.
        """
        cdef SynthResult r = SynthResult()
        r.cr = self.csolver.checkSynthNext()
        return r

    def getSynthSolution(self, Term term):
        """
        Get the synthesis solution of the given term. This method should be
        called immediately after the solver answers unsat for sygus input.

        :param term: the term for which the synthesis solution is queried
        :return: the synthesis solution of the given term
        """
        cdef Term t = Term(self)
        t.cterm = self.csolver.getSynthSolution(term.cterm)
        return t

    def getSynthSolutions(self, list terms):
        """
        Get the synthesis solutions of the given terms. This method should be
        called immediately after the solver answers unsat for sygus input.

        :param terms: the terms for which the synthesis solutions is queried
        :return: the synthesis solutions of the given terms
        """
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
        """
        Synthesize invariant.

        SyGuS v2:

        .. code-block:: smtlib

            ( synth-inv <symbol> ( <boundVars>* ) <grammar> )

        :param symbol: the name of the invariant
        :param boundVars: the parameters to this invariant
        :param grammar: the syntactic constraints
        :return: the invariant
        """
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
        """ Check satisfiability assuming the given formula.

        SMT-LIB:

        .. code-block:: smtlib

            ( check-sat-assuming ( <prop_literal> ) )

        :param assumptions: the formulas to assume, as a list or as distinct arguments
        :return: the result of the satisfiability check.
        """
        cdef Result r = Result()
        # used if assumptions is a list of terms
        cdef vector[c_Term] v
        for a in assumptions:
            v.push_back((<Term?> a).cterm)
        r.cr = self.csolver.checkSatAssuming(<const vector[c_Term]&> v)
        return r

    @expand_list_arg(num_req_args=1)
    def declareDatatype(self, str symbol, *ctors):
        """
        Create datatype sort.

        SMT-LIB:

        .. code-block:: smtlib

            ( declare-datatype <symbol> <datatype_decl> )

        :param symbol: the name of the datatype sort
        :param ctors: the constructor declarations of the datatype sort, as a list or as distinct arguments
        :return: the datatype sort
        """
        cdef Sort sort = Sort(self)
        cdef vector[c_DatatypeConstructorDecl] v

        for c in ctors:
            v.push_back((<DatatypeConstructorDecl?> c).cddc)
        sort.csort = self.csolver.declareDatatype(symbol.encode(), v)
        return sort

    def declareFun(self, str symbol, list sorts, Sort sort):
        """Declare n-ary function symbol.

        SMT-LIB:

        .. code-block:: smtlib

            ( declare-fun <symbol> ( <sort>* ) <sort> )

        :param symbol: the name of the function
        :param sorts: the sorts of the parameters to this function
        :param sort: the sort of the return value of this function
        :return: the function
        """
        cdef Term term = Term(self)
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        term.cterm = self.csolver.declareFun(symbol.encode(),
                                             <const vector[c_Sort]&> v,
                                             sort.csort)
        return term

    def declareSort(self, str symbol, int arity):
        """Declare uninterpreted sort.

        SMT-LIB:

        .. code-block:: smtlib

            ( declare-sort <symbol> <numeral> )

        .. note::
          This corresponds to :py:meth:`Solver.mkUninterpretedSort()` if
          arity = 0, and to
          :py:meth:`Solver.mkUninterpretedSortConstructorSort()` if arity > 0.

        :param symbol: the name of the sort
        :param arity: the arity of the sort
        :return: the sort
        """
        cdef Sort sort = Sort(self)
        sort.csort = self.csolver.declareSort(symbol.encode(), arity)
        return sort

    def defineFun(self, str symbol, list bound_vars, Sort sort, Term term, glbl=False):
        """Define n-ary function.

        SMT-LIB:

        .. code-block:: smtlib

            ( define-fun <function_def> )

        :param symbol: the name of the function
        :param bound_vars: the parameters to this function
        :param sort: the sort of the return value of this function
        :param term: the function body
        :param glbl: determines whether this definition is global (i.e. persists when popping the context)
        :return: the function
        """
        cdef Term fun = Term(self)
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)

        fun.cterm = self.csolver.defineFun(symbol.encode(),
                                           <const vector[c_Term] &> v,
                                           sort.csort,
                                           term.cterm,
                                           <bint> glbl)
        return fun

    def defineFunRec(self, sym_or_fun, bound_vars, sort_or_term, t=None, glbl=False):
        """Define recursive functions.

        Supports two uses:

        - ``Term defineFunRec(str symbol, List[Term] bound_vars, Sort sort, Term term, bool glbl)``
        - ``Term defineFunRec(Term fun, List[Term] bound_vars, Term term, bool glbl)``


        SMT-LIB:

        .. code-block:: smtlib

            ( define-funs-rec ( <function_decl>^n ) ( <term>^n ) )

        Create elements of parameter ``funs`` with mkConst().

        :param funs: the sorted functions
        :param bound_vars: the list of parameters to the functions
        :param terms: the list of function bodies of the functions
        :param global: determines whether this definition is global (i.e. persists when popping the context)
        :return: the function
        """
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
        """Define recursive functions.

        SMT-LIB:

        .. code-block:: smtlib

            ( define-funs-rec ( <function_decl>^n ) ( <term>^n ) )

        Create elements of parameter ``funs`` with mkConst().

        :param funs: the sorted functions
        :param bound_vars: the list of parameters to the functions
        :param terms: the list of function bodies of the functions
        :param global: determines whether this definition is global (i.e. persists when popping the context)
        :return: the function
        """
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

    def getProof(self):
        """Get the refutation proof

        SMT-LIB:

        .. code-block:: smtlib
        
           (get-proof)

        Requires to enable option
        :ref:`produce-proofs <lbl-option-produce-proofs>`.

        .. warning:: This method is experimental and may change in future
                     versions.

        :return: a string representing the proof, according to the value of
                 proof-format-mode.
        """
        return self.csolver.getProof()

    def getLearnedLiterals(self):
        """Get a list of literals that are entailed by the current set of assertions

        SMT-LIB:

        .. code-block:: smtlib

            ( get-learned-literals )

        .. warning:: This method is experimental and may change in future
                     versions.

        :return: the list of literals
        """
        lits = []
        for a in self.csolver.getLearnedLiterals():
            term = Term(self)
            term.cterm = a
            lits.append(term)
        return lits

    def getAssertions(self):
        """Get the list of asserted formulas.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-assertions )

        :return: the list of asserted formulas
        """
        assertions = []
        for a in self.csolver.getAssertions():
            term = Term(self)
            term.cterm = a
            assertions.append(term)
        return assertions

    def getInfo(self, str flag):
        """
        Get info from the solver.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-info <info_flag> )

        :param flag: the info flag
        :return: the info
        """
        return self.csolver.getInfo(flag.encode())

    def getOption(self, str option):
        """Get the value of a given option.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-option <keyword> )

        :param option: the option for which the value is queried
        :return: a string representation of the option value
        """
        return self.csolver.getOption(option.encode()).decode()

    def getOptionNames(self):
        """Get all option names that can be used with `setOption`, `getOption` and `getOptionInfo`.

        :return: all option names
        """
        return [s.decode() for s in self.csolver.getOptionNames()]

    def getOptionInfo(self, str option):
        """Get some information about the given option. Check the `OptionInfo`
        class for more details on which information is available.

        :return: information about the given option
        """
        # declare all the variables we may need later
        cdef c_OptionInfo.ValueInfo[c_bool] vib
        cdef c_OptionInfo.ValueInfo[string] vis
        cdef c_OptionInfo.NumberInfo[int64_t] nii
        cdef c_OptionInfo.NumberInfo[uint64_t] niu
        cdef c_OptionInfo.NumberInfo[double] nid
        cdef c_OptionInfo.ModeInfo mi

        oi = self.csolver.getOptionInfo(option.encode())
        # generic information
        res = {
            'name': oi.name.decode(),
            'aliases': [s.decode() for s in oi.aliases],
            'setByUser': oi.setByUser,
        }

        # now check which type is actually in the variant
        if c_holds[c_OptionInfo.VoidInfo](oi.valueInfo):
            # it's a void
            res['type'] = None
        elif c_holds[c_OptionInfo.ValueInfo[c_bool]](oi.valueInfo):
            # it's a bool
            res['type'] = bool
            vib = c_getVariant[c_OptionInfo.ValueInfo[c_bool]](oi.valueInfo)
            res['current'] = vib.currentValue
            res['default'] = vib.defaultValue
        elif c_holds[c_OptionInfo.ValueInfo[string]](oi.valueInfo):
            # it's a string
            res['type'] = str
            vis = c_getVariant[c_OptionInfo.ValueInfo[string]](oi.valueInfo)
            res['current'] = vis.currentValue.decode()
            res['default'] = vis.defaultValue.decode()
        elif c_holds[c_OptionInfo.NumberInfo[int64_t]](oi.valueInfo):
            # it's an int64_t
            res['type'] = int
            nii = c_getVariant[c_OptionInfo.NumberInfo[int64_t]](oi.valueInfo)
            res['current'] = nii.currentValue
            res['default'] = nii.defaultValue
            res['minimum'] = nii.minimum.value() if nii.minimum.has_value() else None
            res['maximum'] = nii.maximum.value() if nii.maximum.has_value() else None
        elif c_holds[c_OptionInfo.NumberInfo[uint64_t]](oi.valueInfo):
            # it's a uint64_t
            res['type'] = int
            niu = c_getVariant[c_OptionInfo.NumberInfo[uint64_t]](oi.valueInfo)
            res['current'] = niu.currentValue
            res['default'] = niu.defaultValue
            res['minimum'] = niu.minimum.value() if niu.minimum.has_value() else None
            res['maximum'] = niu.maximum.value() if niu.maximum.has_value() else None
        elif c_holds[c_OptionInfo.NumberInfo[double]](oi.valueInfo):
            # it's a double
            res['type'] = float
            nid = c_getVariant[c_OptionInfo.NumberInfo[double]](oi.valueInfo)
            res['current'] = nid.currentValue
            res['default'] = nid.defaultValue
            res['minimum'] = nid.minimum.value() if nid.minimum.has_value() else None
            res['maximum'] = nid.maximum.value() if nid.maximum.has_value() else None
        elif c_holds[c_OptionInfo.ModeInfo](oi.valueInfo):
            # it's a mode
            res['type'] = 'mode'
            mi = c_getVariant[c_OptionInfo.ModeInfo](oi.valueInfo)
            res['current'] = mi.currentValue.decode()
            res['default'] = mi.defaultValue.decode()
            res['modes'] = [s.decode() for s in mi.modes]
        return res

    def getOptionNames(self):
       """Get all option names that can be used with `setOption`, `getOption` and `getOptionInfo`.
       :return: all option names
       """
       result = []
       for n in self.csolver.getOptionNames():
           result += [n.decode()]
       return result

    def getUnsatAssumptions(self):
        """
        Get the set of unsat ("failed") assumptions.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-unsat-assumptions )

        Requires to enable option :ref:`produce-unsat-assumptions <lbl-option-produce-unsat-assumptions>`.

        :return: the set of unsat assumptions.
        """
        assumptions = []
        for a in self.csolver.getUnsatAssumptions():
            term = Term(self)
            term.cterm = a
            assumptions.append(term)
        return assumptions

    def getUnsatCore(self):
        """Get the unsatisfiable core.

        SMT-LIB:

        .. code-block:: smtlib

          (get-unsat-core)

        Requires to enable option :ref:`produce-unsat-cores <lbl-option-produce-unsat-cores>`.

        .. note::
          In contrast to SMT-LIB, the API does not distinguish between named and
          unnamed assertions when producing an unsatisfiable core. Additionally,
          the API allows this option to be called after a check with assumptions.
          A subset of those assumptions may be included in the unsatisfiable core
          returned by this method.

        :return: a set of terms representing the unsatisfiable core
        """
        core = []
        for a in self.csolver.getUnsatCore():
            term = Term(self)
            term.cterm = a
            core.append(term)
        return core

    def getDifficulty(self):
        """
            Get a difficulty estimate for an asserted formula. This method is intended to be called immediately after 
            any response to a checkSat.

            .. warning:: This method is experimental and may change in future
                         versions.

            :return: a map from (a subset of) the input assertions to a real value that is an estimate of how difficult each assertion was to solver. Unmentioned assertions can be assumed to have zero difficulty.
        """
        diffi = {}
        for p in self.csolver.getDifficulty():
            k = p.first
            v = p.second

            termk = Term(self)
            termk.cterm = k

            termv = Term(self)
            termv.cterm = v

            diffi[termk] = termv
        return diffi

    def getValue(self, Term t):
        """Get the value of the given term in the current model.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-value ( <term> ) )

        :param term: the term for which the value is queried
        :return: the value of the given term
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.getValue(t.cterm)
        return term

    def getModelDomainElements(self, Sort s):
        """
        Get the domain elements of uninterpreted sort s in the current model. The
        current model interprets s as the finite sort whose domain elements are
        given in the return value of this method.

        :param s: The uninterpreted sort in question
        :return: the domain elements of s in the current model
        """
        result = []
        cresult = self.csolver.getModelDomainElements(s.csort)
        for e in cresult:
            term = Term(self)
            term.cterm = e
            result.append(term)
        return result

    def isModelCoreSymbol(self, Term v):
        """
        This returns false if the model value of free constant v was not
        essential for showing the satisfiability of the last call to checkSat
        using the current model. This method will only return false (for any v)
        if the model-cores option has been set.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param v: The term in question
        :return: true if v is a model core symbol
        """
        return self.csolver.isModelCoreSymbol(v.cterm)

    def getQuantifierElimination(self, Term term):
        """Do quantifier elimination.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-qe <q> )

        Requires a logic that supports quantifier elimination.
        Currently, the only logics supported by quantifier elimination
        are LRA and LIA.

        .. warning:: This method is experimental and may change in future
                         versions.

        :param q: a quantified formula of the form
                :math:`Q\bar{x}_1... Q\bar{x}_n. P( x_1...x_i, y_1...y_j)'
                where
                :math:'Q\bar{x}' is a set of quantified variables of the form
                :math:'Q x_1...x_k' and
                :math:'P( x_1...x_i, y_1...y_j )' is a quantifier-free formula
        :return: a formula :math:'\phi'  such that, given the current set of formulas
               :math:'A asserted to this solver:
               - :math:'(A \wedge q)' :math:'(A \wedge \phi)' are equivalent
               - :math:'\phi' is quantifier-free formula containing only free
                 variables in :math:'y_1...y_n'.
        """
        cdef Term result = Term(self)
        result.cterm = self.csolver.getQuantifierElimination(term.cterm)
        return result

    def getQuantifierEliminationDisjunct(self, Term term):
        """Do partial quantifier elimination, which can be used for incrementally computing
        the result of a quantifier elimination.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-qe-disjunct <q> )

        Requires a logic that supports quantifier elimination.
        Currently, the only logics supported by quantifier elimination
        are LRA and LIA.
            
	.. warning:: This method is experimental and may change in future
                         versions.
        
           :param q: a quantified formula of the form
                   @f$Q\bar{x}_1... Q\bar{x}_n. P( x_1...x_i, y_1...y_j)@f$
                   where
                   @f$Q\bar{x}@f$ is a set of quantified variables of the form
                   @f$Q x_1...x_k@f$ and
                   @f$P( x_1...x_i, y_1...y_j )@f$ is a quantifier-free formula
           :return: a formula @f$\phi@f$ such that, given the current set of formulas
                  @f$A@f$ asserted to this solver:
                  - @f$(A \wedge q \implies A \wedge \phi)@f$ if @f$Q@f$ is
                    @f$\forall@f$, and @f$(A \wedge \phi \implies A \wedge q)@f$ if
                    @f$Q@f$ is @f$\exists@f$
                  - @f$\phi@f$ is quantifier-free formula containing only free
                    variables in @f$y_1...y_n@f$
                  - If @f$Q@f$ is @f$\exists@f$, let @f$(A \wedge Q_n)@f$ be the
                    formula
                    @f$(A \wedge \neg (\phi \wedge Q_1) \wedge ... \wedge
                    \neg (\phi \wedge Q_n))@f$
                    where for each @f$i = 1...n@f$,
                    formula @f$(\phi \wedge Q_i)@f$ is the result of calling
                    Solver::getQuantifierEliminationDisjunct() for @f$q@f$ with the
                    set of assertions @f$(A \wedge Q_{i-1})@f$.
                    Similarly, if @f$Q@f$ is @f$\forall@f$, then let
                    @f$(A \wedge Q_n)@f$ be
                    @f$(A \wedge (\phi \wedge Q_1) \wedge ... \wedge (\phi \wedge
                    Q_n))@f$
                    where @f$(\phi \wedge Q_i)@f$ is the same as above.
                    In either case, we have that @f$(\phi \wedge Q_j)@f$ will
                    eventually be true or false, for some finite j.
        """
        cdef Term result = Term(self)
        result.cterm = self.csolver.getQuantifierEliminationDisjunct(term.cterm)
        return result
    
    def getModel(self, sorts, consts):
        """Get the model

        SMT-LIB:

        .. code:: smtlib
        
            (get-model)

        Requires to enable option
        :ref:`produce-models <lbl-option-produce-models>`.

        .. warning:: This method is experimental and may change in future
                     versions.
   
        :param sorts: The list of uninterpreted sorts that should be printed in
                      the model.
        :param vars: The list of free constants that should be printed in the
                     model. A subset of these may be printed based on
                     isModelCoreSymbol.
        :return: a string representing the model.
        """

        cdef vector[c_Sort] csorts
        for sort in sorts:
            csorts.push_back((<Sort?> sort).csort)

        cdef vector[c_Term] cconsts
        for const in consts:
            cconsts.push_back((<Term?> const).cterm)

        return self.csolver.getModel(csorts, cconsts)

    def getValueSepHeap(self):
        """When using separation logic, obtain the term for the heap.

        .. warning:: This method is experimental and may change in future
                     versions.

        :return: The term for the heap
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.getValueSepHeap()
        return term

    def getValueSepNil(self):
        """When using separation logic, obtain the term for nil.

        .. warning:: This method is experimental and may change in future
                     versions.

        :return: The term for nil
        """
        cdef Term term = Term(self)
        term.cterm = self.csolver.getValueSepNil()
        return term

    def declareSepHeap(self, Sort locType, Sort dataType):
        """
        When using separation logic, this sets the location sort and the
        datatype sort to the given ones. This method should be invoked exactly
        once, before any separation logic constraints are provided.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param locSort: The location sort of the heap
        :param dataSort: The data sort of the heap
        """
        self.csolver.declareSepHeap(locType.csort, dataType.csort)

    def declarePool(self, str symbol, Sort sort, initValue):
        """Declare a symbolic pool of terms with the given initial value.

        SMT-LIB:

        .. code-block:: smtlib

            ( declare-pool <symbol> <sort> ( <term>* ) )

        .. warning:: This method is experimental and may change in future
                     versions.

        :param symbol: The name of the pool
        :param sort: The sort of the elements of the pool.
        :param initValue: The initial value of the pool
        """
        cdef Term term = Term(self)
        cdef vector[c_Term] niv
        for v in initValue:
            niv.push_back((<Term?> v).cterm)
        term.cterm = self.csolver.declarePool(symbol.encode(), sort.csort, niv)
        return term

    def pop(self, nscopes=1):
        """Pop ``nscopes`` level(s) from the assertion stack.

        SMT-LIB:

        .. code-block:: smtlib

            ( pop <numeral> )

        :param nscopes: the number of levels to pop
        """
        self.csolver.pop(nscopes)

    def push(self, nscopes=1):
        """ Push ``nscopes`` level(s) to the assertion stack.

        SMT-LIB:

        .. code-block:: smtlib

            ( push <numeral> )

        :param nscopes: the number of levels to push
        """
        self.csolver.push(nscopes)

    def resetAssertions(self):
        """
        Remove all assertions.

        SMT-LIB:

        .. code-block:: smtlib

            ( reset-assertions )

        """
        self.csolver.resetAssertions()

    def setInfo(self, str keyword, str value):
        """Set info.

        SMT-LIB:

        .. code-block:: smtlib

            ( set-info <attribute> )

        :param keyword: the info flag
        :param value: the value of the info flag
        """
        self.csolver.setInfo(keyword.encode(), value.encode())

    def setLogic(self, str logic):
        """Set logic.

        SMT-LIB:

        .. code-block:: smtlib

            ( set-logic <symbol> )

        :param logic: the logic to set
        """
        self.csolver.setLogic(logic.encode())

    def setOption(self, str option, str value):
        """Set option.

        SMT-LIB:

        .. code-block:: smtlib

            ( set-option <option> )

        :param option: the option name
        :param value: the option value
        """
        self.csolver.setOption(option.encode(), value.encode())


    def getInterpolant(self, Term conj, *args):
        """Get an interpolant.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-interpolant <conj> )
            ( get-interpolant <conj> <grammar> )

        Requires option :ref:`produce-interpolants <lbl-option-produce-interpolants>` to be set to a mode different from `none`.

        Supports the following variants:

        - ``Term getInteprolant(Term conj)``
        - ``Term getInteprolant(Term conj, Grammar grammar)``

        .. warning:: This method is experimental and may change in future
                     versions.
        
        :param conj: the conjecture term
        :param output: the term where the result will be stored
        :param grammar: a grammar for the inteprolant
        :return: True iff an interpolant was found
        """
        cdef Term result = Term(self)
        if len(args) == 0:
            result.cterm = self.csolver.getInterpolant(conj.cterm)
        else:
            assert len(args) == 1
            assert isinstance(args[0], Grammar)
            result.cterm = self.csolver.getInterpolant(conj.cterm, (<Grammar ?> args[0]).cgrammar)
        return result


    def getInterpolantNext(self):
        """
        Get the next interpolant. Can only be called immediately after
        a succesful call to get-interpolant or get-interpolant-next. 
        Is guaranteed to produce a syntactically different interpolant wrt the
        last returned interpolant if successful.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-interpolant-next )

        Requires to enable incremental mode, and 
        option :ref:`produce-interpolants <lbl-option-produce-interpolants>` to be set to a mode different from `none`.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param output: the term where the result will be stored
        :return: True iff an interpolant was found
        """
        cdef Term result = Term(self)
        result.cterm = self.csolver.getInterpolantNext()
        return result
        
    def getAbduct(self, Term conj, *args):
        """Get an abduct.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-abduct <conj> )
            ( get-abduct <conj> <grammar> )

        Requires to enable option :ref:`produce-abducts <lbl-option-produce-abducts>`.

        Supports the following variants:

        - ``Term getAbduct(Term conj)``
        - ``Term getAbduct(Term conj, Grammar grammar)``

        .. warning:: This method is experimental and may change in future
                     versions.
        
        :param conj: the conjecture term
        :param output: the term where the result will be stored
        :param grammar: a grammar for the abduct 
        :return: True iff an abduct was found
        """
        cdef Term result = Term(self)
        if len(args) == 0:
            result.cterm  = self.csolver.getAbduct(conj.cterm)
        else:
            assert len(args) == 1
            assert isinstance(args[0], Grammar)
            result.cterm = self.csolver.getAbduct(conj.cterm, (<Grammar ?> args[0]).cgrammar)
        return result

    def getAbductNext(self):
        """
        Get the next abduct. Can only be called immediately after
        a succesful call to get-abduct or get-abduct-next. 
        Is guaranteed to produce a syntactically different abduct wrt the 
        last returned abduct if successful.

        SMT-LIB:

        .. code-block:: smtlib

            ( get-abduct-next )

        Requires to enable incremental mode, and 
        option :ref:`produce-abducts <lbl-option-produce-abducts>`.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param output: the term where the result will be stored
        :return: True iff an abduct was found
        """
        cdef Term result = Term(self)
        result.cterm  = self.csolver.getAbductNext()
        return result

    def blockModel(self):
        """
        Block the current model. Can be called only if immediately preceded by a
        SAT or INVALID query.

        SMT-LIB:

        .. code-block:: smtlib
        
            (block-model)

        Requires enabling option
        :ref:`produce-models <lbl-option-produce-models>`
        and setting option
        :ref:`block-models <lbl-option-block-models>`
        to a mode other than ``none``.

        .. warning:: This method is experimental and may change in future
                     versions.
        """
        self.csolver.blockModel()

    def blockModelValues(self, terms):
        """
        Block the current model values of (at least) the values in terms. Can be
        called only if immediately preceded by a SAT or NOT_ENTAILED query.

        SMT-LIB:

        .. code-block:: smtlib

           (block-model-values ( <terms>+ ))

        Requires enabling option
        :ref:`produce-models <lbl-option-produce-models>`.

        .. warning:: This method is experimental and may change in future
                     versions.
        """
        cdef vector[c_Term] nts
        for t in terms:
            nts.push_back((<Term?> t).cterm)
        self.csolver.blockModelValues(nts)

    def getInstantiations(self):
        """
        Return a string that contains information about all instantiations made
        by the quantifiers module.

        .. warning:: This method is experimental and may change in future
                     versions.
        """
        return self.csolver.getInstantiations()

    def getStatistics(self):
        """
        Returns a snapshot of the current state of the statistic values of this
        solver. The returned object is completely decoupled from the solver and
        will not change when the solver is used again.
        """
        res = Statistics()
        res.cstats = self.csolver.getStatistics()
        return res


cdef class Sort:
    """
    The sort of a cvc5 term.
    """
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

    def hasSymbol(self):
        """:return: True iff this sort has a symbol."""
        return self.csort.hasSymbol()

    def getSymbol(self):
        """
        Asserts :py:meth:`hasSymbol()`.

        :return: the raw symbol of the sort.
        """
        return self.csort.getSymbol().decode()

    def isNull(self):
        """:return: True if this Sort is a null sort."""
        return self.csort.isNull()

    def isBoolean(self):
        """
            Is this a Boolean sort?

            :return: True if the sort is the Boolean sort.
        """
        return self.csort.isBoolean()

    def isInteger(self):
        """
            Is this an integer sort?

            :return: True if the sort is the integer sort.
        """
        return self.csort.isInteger()

    def isReal(self):
        """
            Is this a real sort?

            :return: True if the sort is the real sort.
        """
        return self.csort.isReal()

    def isString(self):
        """
            Is this a string sort?

            :return: True if the sort is the string sort.
        """
        return self.csort.isString()

    def isRegExp(self):
        """
            Is this a regexp sort?

            :return: True if the sort is the regexp sort.
        """
        return self.csort.isRegExp()

    def isRoundingMode(self):
        """
            Is this a rounding mode sort?

            :return: True if the sort is the rounding mode sort.
        """
        return self.csort.isRoundingMode()

    def isBitVector(self):
        """
            Is this a bit-vector sort?

            :return: True if the sort is a bit-vector sort.
        """
        return self.csort.isBitVector()

    def isFloatingPoint(self):
        """
            Is this a floating-point sort?

            :return: True if the sort is a bit-vector sort.
        """
        return self.csort.isFloatingPoint()

    def isDatatype(self):
        """
            Is this a datatype sort?

            :return: True if the sort is a datatype sort.
        """
        return self.csort.isDatatype()

    def isConstructor(self):
        """
            Is this a constructor sort?

            :return: True if the sort is a constructor sort.
        """
        return self.csort.isConstructor()

    def isSelector(self):
        """
            Is this a selector sort?

            :return: True if the sort is a selector sort.
        """
        return self.csort.isSelector()

    def isTester(self):
        """
            Is this a tester sort?

            :return: True if the sort is a selector sort.
        """
        return self.csort.isTester()

    def isUpdater(self):
        """
            Is this a datatype updater sort?

            :return: True if the sort is a datatype updater sort.
        """
        return self.csort.isUpdater()

    def isFunction(self):
        """
            Is this a function sort?

            :return: True if the sort is a function sort.
        """
        return self.csort.isFunction()

    def isPredicate(self):
        """
            Is this a predicate sort?
            That is, is this a function sort mapping to Boolean? All predicate
            sorts are also function sorts.

            :return: True if the sort is a predicate sort.
        """
        return self.csort.isPredicate()

    def isTuple(self):
        """
            Is this a tuple sort?

            :return: True if the sort is a tuple sort.
        """
        return self.csort.isTuple()

    def isRecord(self):
        """
            Is this a record sort?

            .. warning:: This method is experimental and may change in future
                        versions.

            :return: True if the sort is a record sort.
        """
        return self.csort.isRecord()

    def isArray(self):
        """
            Is this an array sort?

            :return: True if the sort is an array sort.
        """
        return self.csort.isArray()

    def isSet(self):
        """
            Is this a set sort?

            :return: True if the sort is a set sort.
        """
        return self.csort.isSet()

    def isBag(self):
        """
            Is this a bag sort?

            :return: True if the sort is a bag sort.
        """
        return self.csort.isBag()

    def isSequence(self):
        """
            Is this a sequence sort?

            :return: True if the sort is a sequence sort.
        """
        return self.csort.isSequence()

    def isUninterpretedSort(self):
        """
            Is this a sort uninterpreted?

            :return: True if the sort is uninterpreted.
        """
        return self.csort.isUninterpretedSort()

    def isUninterpretedSortConstructor(self):
        """
            Is this a sort constructor kind?

            An uninterpreted sort constructor is an uninterpreted sort with
            arity > 0.

            :return: True if this a sort constructor kind.
        """
        return self.csort.isUninterpretedSortConstructor()

    def isInstantiated(self):
        """
            Is this an instantiated (parametric datatype or uninterpreted sort
            constructor) sort?

            An instantiated sort is a sort that has been constructed from
            instantiating a sort parameters with sort arguments
            (see Sort::instantiate()).

            :return: True if this is an instantiated sort.
        """
        return self.csort.isInstantiated()

    def getUninterpretedSortConstructor(self):
        """
            Get the associated uninterpreted sort constructor of an
            instantiated uninterpreted sort.

            :return: the uninterpreted sort constructor sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getUninterpretedSortConstructor()
        return sort

    def getDatatype(self):
        """
            :return: the underlying datatype of a datatype sort
        """
        cdef Datatype d = Datatype(self.solver)
        d.cd = self.csort.getDatatype()
        return d

    def instantiate(self, params):
        """
            Instantiate a parameterized datatype sort or uninterpreted sort
            constructor sort.
            Create sorts parameter with :py:meth:`Solver.mkParamSort()`

            .. warning:: This method is experimental and may change in future
                         versions.

            :param params: the list of sort parameters to instantiate with
            :return: the instantiated sort
        """
        cdef Sort sort = Sort(self.solver)
        cdef vector[c_Sort] v
        for s in params:
            v.push_back((<Sort?> s).csort)
        sort.csort = self.csort.instantiate(v)
        return sort

    def getInstantiatedParameters(self):
        """
            Get the sorts used to instantiate the sort parameters of a
            parametric sort (parametric datatype or uninterpreted sort
            constructor sort, see Sort.instantiate()).

            :return the sorts used to instantiate the sort parameters of a
                    parametric sort
        """
        instantiated_sorts = []
        for s in self.csort.getInstantiatedParameters():
            sort = Sort(self.solver)
            sort.csort = s
            instantiated_sorts.append(sort)
        return instantiated_sorts

    def substitute(self, sort_or_list_1, sort_or_list_2):
        """
        Substitution of Sorts.

        Note that this replacement is applied during a pre-order traversal and
        only once to the sort. It is not run until fix point. In the case that
        sort_or_list_1 contains duplicates, the replacement earliest in the list
        takes priority.

        For example,
        ``(Array A B) .substitute([A, C], [(Array C D), (Array A B)])`` will
        return ``(Array (Array C D) B)``.

        .. warning:: This method is experimental and may change in future
                     versions.

        :param sort_or_list_1: the subsort or subsorts to be substituted within this sort.
        :param sort_or_list_2: the sort or list of sorts replacing the substituted subsort.
        """

        # The resulting sort after substitution
        cdef Sort sort = Sort(self.solver)
        # lists for substitutions
        cdef vector[c_Sort] ces
        cdef vector[c_Sort] creplacements

        # normalize the input parameters to be lists
        if isinstance(sort_or_list_1, list):
            assert isinstance(sort_or_list_2, list)
            es = sort_or_list_1
            replacements = sort_or_list_2
            if len(es) != len(replacements):
                raise RuntimeError("Expecting list inputs to substitute to "
                                   "have the same length but got: "
                                   "{} and {}".format(len(es), len(replacements)))

            for e, r in zip(es, replacements):
                ces.push_back((<Sort?> e).csort)
                creplacements.push_back((<Sort?> r).csort)

        else:
            # add the single elements to the vectors
            ces.push_back((<Sort?> sort_or_list_1).csort)
            creplacements.push_back((<Sort?> sort_or_list_2).csort)

        # call the API substitute method with lists
        sort.csort = self.csort.substitute(ces, creplacements)
        return sort


    def getConstructorArity(self):
        """
            :return: the arity of a constructor sort.
        """
        return self.csort.getConstructorArity()

    def getConstructorDomainSorts(self):
        """
            :return: the domain sorts of a constructor sort
        """
        domain_sorts = []
        for s in self.csort.getConstructorDomainSorts():
            sort = Sort(self.solver)
            sort.csort = s
            domain_sorts.append(sort)
        return domain_sorts

    def getConstructorCodomainSort(self):
        """
            :return: the codomain sort of a constructor sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getConstructorCodomainSort()
        return sort

    def getSelectorDomainSort(self):
        """
            :return: the domain sort of a selector sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSelectorDomainSort()
        return sort

    def getSelectorCodomainSort(self):
        """
            :return: the codomain sort of a selector sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSelectorCodomainSort()
        return sort

    def getTesterDomainSort(self):
        """
            :return: the domain sort of a tester sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getTesterDomainSort()
        return sort

    def getTesterCodomainSort(self):
        """
            :return: the codomain sort of a tester sort, which is the Boolean sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getTesterCodomainSort()
        return sort

    def getFunctionArity(self):
        """
            :return: the arity of a function sort
        """
        return self.csort.getFunctionArity()

    def getFunctionDomainSorts(self):
        """
            :return: the domain sorts of a function sort
        """
        domain_sorts = []
        for s in self.csort.getFunctionDomainSorts():
            sort = Sort(self.solver)
            sort.csort = s
            domain_sorts.append(sort)
        return domain_sorts

    def getFunctionCodomainSort(self):
        """
            :return: the codomain sort of a function sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getFunctionCodomainSort()
        return sort

    def getArrayIndexSort(self):
        """
            :return: the array index sort of an array sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getArrayIndexSort()
        return sort

    def getArrayElementSort(self):
        """
            :return: the array element sort of an array sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getArrayElementSort()
        return sort

    def getSetElementSort(self):
        """
            :return: the element sort of a set sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSetElementSort()
        return sort

    def getBagElementSort(self):
        """
            :return: the element sort of a bag sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getBagElementSort()
        return sort

    def getSequenceElementSort(self):
        """
            :return: the element sort of a sequence sort
        """
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.csort.getSequenceElementSort()
        return sort

    def getUninterpretedSortConstructorArity(self):
        """
            :return: the arity of a sort constructor sort
        """
        return self.csort.getUninterpretedSortConstructorArity()

    def getBitVectorSize(self):
        """
            :return: the bit-width of the bit-vector sort
        """
        return self.csort.getBitVectorSize()

    def getFloatingPointExponentSize(self):
        """
            :return: the bit-width of the exponent of the floating-point sort
        """
        return self.csort.getFloatingPointExponentSize()

    def getFloatingPointSignificandSize(self):
        """
            :return: the width of the significand of the floating-point sort
        """
        return self.csort.getFloatingPointSignificandSize()

    def getDatatypeArity(self):
        """
            :return: the arity of a datatype sort
        """
        return self.csort.getDatatypeArity()

    def getTupleLength(self):
        """
            :return: the length of a tuple sort
        """
        return self.csort.getTupleLength()

    def getTupleSorts(self):
        """
            :return: the element sorts of a tuple sort
        """
        tuple_sorts = []
        for s in self.csort.getTupleSorts():
            sort = Sort(self.solver)
            sort.csort = s
            tuple_sorts.append(sort)
        return tuple_sorts


cdef class Statistics:
    """
    The cvc5 Statistics.
    Wrapper class for :cpp:class:`cvc5::Statistics`.
    Obtain a single statistic value using ``stats["name"]`` and a dictionary
    with all (visible) statistics using ``stats.get(internal=False, defaulted=False)``.
    """
    cdef c_Statistics cstats

    cdef __stat_to_dict(self, const c_Stat& s):
        res = None
        if s.isInt():
            res = s.getInt()
        elif s.isDouble():
            res = s.getDouble()
        elif s.isString():
            res = s.getString().decode()
        elif s.isHistogram():
            res = { h.first.decode(): h.second for h in s.getHistogram() }
        return {
            'defaulted': s.isDefault(),
            'internal': s.isInternal(),
            'value': res
        }

    def __getitem__(self, str name):
        """Get the statistics information for the statistic called ``name``."""
        return self.__stat_to_dict(self.cstats.get(name.encode()))

    def get(self, bint internal = False, bint defaulted = False):
        """Get all statistics. See :cpp:class:`cvc5::Statistics::begin()` for more information."""
        cdef c_Statistics.iterator it = self.cstats.begin(internal, defaulted)
        cdef pair[string,c_Stat]* s
        res = {}
        while it != self.cstats.end():
            s = &dereference(it)
            res[s.first.decode()] = self.__stat_to_dict(s.second)
            preincrement(it)
        return res


cdef class Term:
    """
    A cvc5 Term.
    Wrapper class for :cpp:class:`cvc5::Term`.
    """
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
        """:return: the number of children of this term."""
        return self.cterm.getNumChildren()

    def getId(self):
        """:return: the id of this term."""
        return self.cterm.getId()

    def getKind(self):
        """:return: the :py:class:`cvc5.Kind` of this term."""
        return Kind(<int> self.cterm.getKind())

    def getSort(self):
        """:return: the :py:class:`cvc5.Sort` of this term."""
        cdef Sort sort = Sort(self.solver)
        sort.csort = self.cterm.getSort()
        return sort

    def substitute(self, term_or_list_1, term_or_list_2):
        """
	   :return: the result of simultaneously replacing the term(s) stored in ``term_or_list_1`` by the term(s) stored in ``term_or_list_2`` in this term.
	   
        Note that this replacement is applied during a pre-order traversal and
        only once to the term. It is not run until fix point. In the case that
        terms contains duplicates, the replacement earliest in the list takes
        priority. For example, calling substitute on ``f(x,y)`` with

        .. code:: python

            term_or_list_1 = [ x, z ], term_or_list_2 = [ g(z), w ]
        
        results in the term ``f(g(z),y)``.
	    """
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
        """:return: True iff this term has an operator."""
        return self.cterm.hasOp()

    def getOp(self):
        """
        .. note:: This is safe to call when :py:meth:`hasOp()` returns True.

        :return: the :py:class:`cvc5.Op` used to create this Term.
        """
        cdef Op op = Op(self.solver)
        op.cop = self.cterm.getOp()
        return op

    def hasSymbol(self):
        """:return: True iff this term has a symbol."""
        return self.cterm.hasSymbol()

    def getSymbol(self):
        """
        Asserts :py:meth:`hasSymbol()`.

        :return: the raw symbol of the term.
        """
        return self.cterm.getSymbol().decode()

    def isNull(self):
        """:return: True iff this term is a null term."""
        return self.cterm.isNull()

    def notTerm(self):
        """
	   Boolean negation.

	   :return: the Boolean negation of this term.
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.notTerm()
        return term

    def andTerm(self, Term t):
        """
	   Boolean and.

           :param t: a Boolean term
	   :return: the conjunction of this term and the given term
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.andTerm((<Term> t).cterm)
        return term

    def orTerm(self, Term t):
        """
	   Boolean or.

           :param t: a Boolean term
	   :return: the disjunction of this term and the given term
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.orTerm(t.cterm)
        return term

    def xorTerm(self, Term t):
        """
	   Boolean exclusive or.

           :param t: a Boolean term
	   :return: the exclusive disjunction of this term and the given term
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.xorTerm(t.cterm)
        return term

    def eqTerm(self, Term t):
        """
	   Equality

           :param t: a Boolean term
	   :return: the Boolean equivalence of this term and the given term
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.eqTerm(t.cterm)
        return term

    def impTerm(self, Term t):
        """
	   Boolean Implication.

           :param t: a Boolean term
	   :return: the implication of this term and the given term
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.impTerm(t.cterm)
        return term

    def iteTerm(self, Term then_t, Term else_t):
        """
	   If-then-else with this term as the Boolean condition.

           :param then_t: the `then` term
           :param else_t: the `else` term
	   :return: the if-then-else term with this term as the Boolean condition
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.iteTerm(then_t.cterm, else_t.cterm)
        return term

    def isConstArray(self):
        """:return: True iff this term is a constant array."""
        return self.cterm.isConstArray()

    def getConstArrayBase(self):
        """
	   Asserts :py:meth:`isConstArray()`.

	   :return: the base (element stored at all indicies) of this constant array
	"""
        cdef Term term = Term(self.solver)
        term.cterm = self.cterm.getConstArrayBase()
        return term

    def isBooleanValue(self):
        """:return: True iff this term is a Boolean value."""
        return self.cterm.isBooleanValue()

    def getBooleanValue(self):
        """
	   Asserts :py:meth:`isBooleanValue()`

	   :return: the representation of a Boolean value as a native Boolean value.
	"""
        return self.cterm.getBooleanValue()

    def isStringValue(self):
        """:return: True iff this term is a string value."""
        return self.cterm.isStringValue()

    def getStringValue(self):
        """
        Asserts :py:meth:`isStringValue()`.

        .. note::
           This method is not to be confused with :py:meth:`__str__()` which
           returns the term in some string representation, whatever data it
           may hold.

        :return: the string term as a native string value.
        """
        cdef Py_ssize_t size
        cdef c_wstring s = self.cterm.getStringValue()
        return PyUnicode_FromWideChar(s.data(), s.size())

    def getRealOrIntegerValueSign(self):
        """
        Get integer or real value sign. Must be called on integer or real values,
        or otherwise an exception is thrown.
        
        :return: 0 if this term is zero, -1 if this term is a negative real or
                 integer value, 1 if this term is a positive real or integer
                 value.
        """
        return self.cterm.getRealOrIntegerValueSign()

    def isIntegerValue(self):
        """:return: True iff this term is an integer value."""
        return self.cterm.isIntegerValue()
    
    def getIntegerValue(self):
        """
	   Asserts :py:meth:`isIntegerValue()`.
	   
	   :return: the integer term as a native python integer.
	"""
        return int(self.cterm.getIntegerValue().decode())

    def isFloatingPointPosZero(self):
        """:return: True iff the term is the floating-point value for positive zero."""
        return self.cterm.isFloatingPointPosZero()

    def isFloatingPointNegZero(self):
        """:return: True iff the term is the floating-point value for negative zero."""
        return self.cterm.isFloatingPointNegZero()

    def isFloatingPointPosInf(self):
        """:return: True iff the term is the floating-point value for positive infinity."""
        return self.cterm.isFloatingPointPosInf()

    def isFloatingPointNegInf(self):
        """:return: True iff the term is the floating-point value for negative infinity."""
        return self.cterm.isFloatingPointNegInf()

    def isFloatingPointNaN(self):
        """:return: True iff the term is the floating-point value for not a number."""
        return self.cterm.isFloatingPointNaN()

    def isFloatingPointValue(self):
        """:return: True iff this term is a floating-point value."""
        return self.cterm.isFloatingPointValue()

    def getFloatingPointValue(self):
        """
	   Asserts :py:meth:`isFloatingPointValue()`.

	   :return: the representation of a floating-point value as a tuple of the exponent width, the significand width and a bit-vector value.
	"""
        cdef c_tuple[uint32_t, uint32_t, c_Term] t = self.cterm.getFloatingPointValue()
        cdef Term term = Term(self.solver)
        term.cterm = get2(t)
        return (get0(t), get1(t), term)

    def isSetValue(self):
        """
        A term is a set value if it is considered to be a (canonical) constant
        set value.  A canonical set value is one whose AST is:

        .. code::

            (union
                (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))

        where ``c1 ... cn`` are values ordered by id such that
        ``c1 > ... > cn`` (see also :cpp:func:`cvc5::Term::operator>()`).

        .. note::
            A universe set term ``(kind SET_UNIVERSE)`` is not considered to be
            a set value.

        :return: True if the term is a set value.
        """
        return self.cterm.isSetValue()

    def getSetValue(self):
        """
	   Asserts :py:meth:`isSetValue()`.

	   :return: the representation of a set value as a set of terms.
	"""
        elems = set()
        for e in self.cterm.getSetValue():
            term = Term(self.solver)
            term.cterm = e
            elems.add(term)
        return elems

    def isSequenceValue(self):
        """:return: True iff this term is a sequence value."""
        return self.cterm.isSequenceValue()

    def getSequenceValue(self):
        """
        Asserts :py:meth:`isSequenceValue()`.

        .. note::
            It is usually necessary for sequences to call
            :py:meth:`Solver.simplify()` to turn a sequence that is constructed
            by, e.g., concatenation of unit sequences, into a sequence value.

        :return: the representation of a sequence value as a vector of terms.
        """
        elems = []
        for e in self.cterm.getSequenceValue():
            term = Term(self.solver)
            term.cterm = e
            elems.append(term)
        return elems

    def isCardinalityConstraint(self):
        """
        .. warning:: This method is experimental and may change in future
                     versions.
	:return: True if the term is a cardinality constraint.
	"""
        return self.cterm.isCardinalityConstraint()

    def getCardinalityConstraint(self):
        """
        .. warning:: This method is experimental and may change in future
                     versions.
	:return: the sort the cardinality constraint is for and its upper bound.
	"""
        cdef pair[c_Sort, uint32_t] p
        p = self.cterm.getCardinalityConstraint()
        cdef Sort sort = Sort(self.solver)
        sort.csort = p.first
        return (sort, p.second)


    def isUninterpretedSortValue(self):
        """:return: True iff this term is a value from an uninterpreted sort."""
        return self.cterm.isUninterpretedSortValue()

    def getUninterpretedSortValue(self):
        """
	   Asserts :py:meth:`isUninterpretedSortValue()`.

	   :return: the representation of an uninterpreted value as a pair of its sort and its index.
	"""
        return self.cterm.getUninterpretedSortValue()

    def isTupleValue(self):
        """:return: True iff this term is a tuple value."""
        return self.cterm.isTupleValue()

    def isRoundingModeValue(self):
        """:return: True if the term is a floating-point rounding mode value."""
        return self.cterm.isRoundingModeValue()

    def getRoundingModeValue(self):
        """
        Asserts isRoundingModeValue().
        :return: the floating-point rounding mode value held by the term.
        """
        return RoundingMode(<int> self.cterm.getRoundingModeValue())

    def getTupleValue(self):
        """
	   Asserts :py:meth:`isTupleValue()`.

	   :return: the representation of a tuple value as a vector of terms.
	"""
        elems = []
        for e in self.cterm.getTupleValue():
            term = Term(self.solver)
            term.cterm = e
            elems.append(term)
        return elems

    def isRealValue(self):
        """
	    .. note:: A term of kind PI is not considered to be a real value.

	    :return: True iff this term is a rational value.
        """
        return self.cterm.isRealValue()

    def getRealValue(self):
        """
	   Asserts :py:meth:`isRealValue()`.

	   :return: the representation of a rational value as a python Fraction.
	"""
        return Fraction(self.cterm.getRealValue().decode())

    def isBitVectorValue(self):
        """:return: True iff this term is a bit-vector value."""
        return self.cterm.isBitVectorValue()

    def getBitVectorValue(self, base = 2):
        """
	   Asserts :py:meth:`isBitVectorValue()`.
	   Supported bases are 2 (bit string), 10 (decimal string) or 16 (hexdecimal string).

	   :return: the representation of a bit-vector value in string representation. 
	"""
        return self.cterm.getBitVectorValue(base).decode()

    def toPythonObj(self):
        """
        Converts a constant value Term to a Python object.

        Currently supports:

          - Boolean -- returns a Python bool
          - Int     -- returns a Python int
          - Real    -- returns a Python Fraction
          - BV      -- returns a Python int (treats BV as unsigned)
          - String  -- returns a Python Unicode string
          - Array   -- returns a Python dict mapping indices to values. the constant base is returned as the default value

        """

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
                if t.getKind().value == c_Kind.STORE:
                    # save the mappings
                    keys.append(t[1].toPythonObj())
                    values.append(t[2].toPythonObj())
                    to_visit.append(t[0])
                else:
                    assert t.getKind().value == c_Kind.CONST_ARRAY
                    base_value = t.getConstArrayBase().toPythonObj()

            assert len(keys) == len(values)
            assert base_value is not None

            # put everything in a dictionary with the constant
            # base as the result for any index not included in the stores
            res = defaultdict(lambda : base_value)
            for k, v in zip(keys, values):
                res[k] = v

            return res
