from collections import defaultdict
from fractions import Fraction
from functools import wraps
import traceback

cimport cpython.ref as cpy_ref
from cython.operator cimport dereference, preincrement
from cpython.unicode cimport PyUnicode_DATA, PyUnicode_KIND, PyUnicode_READ, PyUnicode_FromKindAndData, PyUnicode_4BYTE_KIND

from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t

from libcpp cimport bool as c_bool
from libcpp.pair cimport pair
from libcpp.set cimport set as c_set
from libcpp.string cimport string
from libcpp.vector cimport vector
from libcpp.map cimport map

from cvc5 cimport cout
from cvc5 cimport stringstream
from cvc5 cimport Command as c_Command
from cvc5 cimport Datatype as c_Datatype
from cvc5 cimport DatatypeConstructor as c_DatatypeConstructor
from cvc5 cimport DatatypeConstructorDecl as c_DatatypeConstructorDecl
from cvc5 cimport DatatypeDecl as c_DatatypeDecl
from cvc5 cimport DatatypeSelector as c_DatatypeSelector
from cvc5 cimport Result as c_Result
from cvc5 cimport InputParser as c_InputParser
from cvc5 cimport SymbolManager as c_SymbolManager
from cvc5 cimport SynthResult as c_SynthResult
from cvc5 cimport Op as c_Op
from cvc5 cimport OptionInfo as c_OptionInfo
from cvc5 cimport holds as c_holds
from cvc5 cimport getVariant as c_getVariant
from cvc5 cimport TermManager as c_TermManager
from cvc5 cimport Solver as c_Solver
from cvc5 cimport Plugin as c_Plugin
from cvc5 cimport PyPlugin as c_PyPlugin
from cvc5 cimport Statistics as c_Statistics
from cvc5 cimport Stat as c_Stat
from cvc5 cimport Grammar as c_Grammar
from cvc5 cimport Proof as c_Proof
from cvc5 cimport Sort as c_Sort
from cvc5 cimport Term as c_Term
from cvc5 cimport hash as c_hash
from cvc5 cimport u32string as c_u32string
from cvc5 cimport tuple as c_tuple
from cvc5 cimport get0, get1, get2
from cvc5kinds cimport Kind as c_Kind
from cvc5kinds cimport SortKind as c_SortKind
from cvc5types cimport BlockModelsMode as c_BlockModelsMode
from cvc5types cimport RoundingMode as c_RoundingMode
from cvc5types cimport UnknownExplanation as c_UnknownExplanation
from cvc5types cimport InputLanguage as c_InputLanguage
from cvc5proofrules cimport ProofRewriteRule as c_ProofRewriteRule
from cvc5proofrules cimport ProofRule as c_ProofRule
from cvc5skolemids cimport SkolemId as c_SkolemId

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

# ----------------------------------------------------------------------------
# Utility functions
# ----------------------------------------------------------------------------

cdef Op _op(tm: TermManager, op: c_Op):
  o = Op()
  o.cop = op
  o.tm = tm
  return o

cdef Term _term(tm: TermManager, term: c_Term):
  t = Term()
  t.cterm = term
  t.tm = tm
  return t

cdef Sort _sort(tm: TermManager, sort: c_Sort):
  s = Sort()
  s.csort = sort
  s.tm = tm
  return s

cdef Datatype _datatype(tm: TermManager, dt: c_Datatype):
  d = Datatype()
  d.cdt = dt
  d.tm = tm
  return d

cdef DatatypeDecl _dtdecl(tm: TermManager, decl: c_DatatypeDecl):
  d = DatatypeDecl()
  d.cdtdecl = decl
  d.tm = tm
  return d

cdef DatatypeConstructor _dtcons(
    tm: TermManager, cons: c_DatatypeConstructor):
  d = DatatypeConstructor()
  d.cdtcons = cons
  d.tm = tm
  return d

cdef DatatypeConstructorDecl _dtconsdecl(
    tm: TermManager, decl: c_DatatypeConstructorDecl):
  d = DatatypeConstructorDecl()
  d.cdtconsdecl = decl
  d.tm = tm
  return d

cdef DatatypeSelector _dtsel(tm: TermManager, sel: c_DatatypeSelector):
  d = DatatypeSelector()
  d.cdtsel = sel
  d.tm = tm
  return d

cdef Grammar _grammar(tm: TermManager, grammar: c_Grammar):
  g = Grammar()
  g.cgrammar = grammar
  g.tm = tm
  return g

cdef Proof _proof(tm: TermManager, proof: c_Proof):
  p = Proof()
  p.cproof = proof
  p.tm = tm
  return p


# ----------------------------------------------------------------------------
# Objects for hashing
# ----------------------------------------------------------------------------

cdef c_hash[c_Op] cophash = c_hash[c_Op]()
cdef c_hash[c_Sort] csorthash = c_hash[c_Sort]()
cdef c_hash[c_Term] ctermhash = c_hash[c_Term]()
cdef c_hash[c_Grammar] cgrammarhash = c_hash[c_Grammar]()
cdef c_hash[c_Proof] cproofhash = c_hash[c_Proof]()

# ----------------------------------------------------------------------------
# SymbolManager
# ----------------------------------------------------------------------------

cdef class SymbolManager:
    """
        Symbol manager. Internally, this class manages a symbol table and other
        meta-information pertaining to SMT2 file inputs (e.g. named assertions,
        declared functions, etc.).

        A symbol manager can be modified by invoking commands, see :py:meth:`Command.invoke`.

        A symbol manager can be provided when constructing an InputParser, in which
        case that InputParser has symbols of this symbol manager preloaded.

        The symbol manager's interface is otherwise not publicly available.

        Wrapper class for the C++ class :cpp:class:`cvc5::parser::SymbolManager`.
    """
    cdef c_SymbolManager* csm
    cdef TermManager tm

    def __cinit__(self, tm):
        """
            Constructor.
            Initialize with associated Solver or TermManager instance.

            .. warning::

                Initializing with associated solver instance is deprecated and
                will be removed in a future release.
        """
        if isinstance(tm, TermManager):
            self.csm = new c_SymbolManager(dereference((<TermManager?>tm).ctm))
            self.tm = tm
        # backwards compatibility, deprecated
        elif isinstance(tm, Solver):
            self.csm = new c_SymbolManager(dereference((<Solver?>tm).tm.ctm))
            self.tm = (<Solver?>tm).tm
        else:
          raise ValueError("Expecting a TermManager or Solver argument")

    def __dealloc__(self):
        del self.csm

    def isLogicSet(self):
        """
            :return: True if the logic of this symbol manager has been set.
        """
        return self.csm.isLogicSet()

    def getLogic(self):
        """
            .. note:: Asserts :py:meth:`isLogicSet()`.

            :return: The logic used by this symbol manager.
        """
        return self.csm.getLogic().decode()

    def getDeclaredSorts(self):
        """
            Get the list of sorts that have been declared via declare-sort.
            These are the sorts that are printed in response to a
            get-model command.

            :return: The declared sorts.
        """
        return [_sort(self.tm, c) for c in self.csm.getDeclaredSorts()]

    def getDeclaredTerms(self):
        """
            Get the list of terms that have been declared via declare-fun and
            declare-const. These are the terms that are printed in response to a
            get-model command.

            :return: The declared terms.
        """
        return [_term(self.tm, c) for c in self.csm.getDeclaredTerms()]

    def getNamedTerms(self):
        """
            Get a mapping from terms to names that have been given to them via
            the :named attribute.

            :return: A map of the named terms to their names.
        """
        namedi = {}
        for p in self.csm.getNamedTerms():
            k = p.first
            v = p.second
            termk = _term(self.tm, k)
            termv = v.decode()
            namedi[termk] = termv
        return namedi

# ----------------------------------------------------------------------------
# Command
# ----------------------------------------------------------------------------

cdef class Command:
    """
        Encapsulation of a command.

        Commands are constructed by the input parser and can be invoked on
        the solver and symbol manager.

        Wrapper class for the C++ class :cpp:class:`cvc5::parser::Command`.
    """
    cdef c_Command cc

    def __str__(self):
        return self.cc.toString().decode()

    def __repr__(self):
        return self.cc.toString().decode()

    def toString(self):
        """
            :return: A string representation of this result.
        """
        return self.cc.toString().decode()

    def invoke(self, Solver solver, SymbolManager sm):
        """
            Invoke the command on the solver and symbol manager, and returns the result.

            :param solver: The solver to invoke the command on.
            :param sm: The symbol manager to invoke the command on.
            :return: A string representation of the result.
        """
        cdef stringstream ss
        self.cc.invoke(solver.csolver, sm.csm, ss)
        return ss.str().decode()

    def getCommandName(self):
        """
            Get the name for this command, e.g. "assert".

            :return: The name of this command.
        """
        return self.cc.getCommandName().decode()

    def isNull(self):
        """
            :return: True if this command is null.
        """
        return self.cc.isNull()


# ----------------------------------------------------------------------------
# InputParser
# ----------------------------------------------------------------------------

cdef class InputParser:
    """
        This class is the main interface for retrieving commands and expressions
        from an input using a parser.

        After construction, it is expected that an input is first set via e.g.
        :py:meth:`setFileInput`, :py:meth:`setStringInput`, or
        :py:meth:`setIncrementalStringInput` and :py:meth:`appendIncrementalStringInput`.
        Then, the methods :py:meth:`nextCommand` and
        :py:meth:`nextExpression` can be invoked to parse the input.

        The input parser interacts with a symbol manager, which determines which
        symbols are defined in the current context, based on the background logic
        and user-defined symbols. If no symbol manager is provided, then the
        input parser will construct (an initially empty) one.

        If provided, the symbol manager must have a logic that is compatible
        with the provided solver. That is, if both the solver and symbol
        manager have their logics set (:py:meth:`SymbolManager.isLogicSet` and
        :py:meth:`Solver.isLogicSet`), then their logics must be the same.

        Upon setting an input source, if either the solver (resp. symbol
        manager) has its logic set, then the symbol manager (resp. solver) is set to
        use that logic, if its logic is not already set.

        Wrapper class for the C++ class :cpp:class:`cvc5::parser::InputParser`.
    """
    cdef c_InputParser* cip
    cdef Solver solver
    cdef SymbolManager sm

    def __cinit__(self, Solver solver, SymbolManager sm=None):
        self.solver = solver
        if sm is None:
            self.sm = SymbolManager(solver.tm)
        else:
            self.sm = sm

        self.cip = new c_InputParser(solver.csolver, self.sm.csm)

    def __dealloc__(self):
        del self.cip

    def getSolver(self):
        """
            :return: The underlying solver of this input parser.
        """
        return self.solver

    def getSymbolManager(self):
        """
            :return: The underlying symbol manager of this input parser.
        """
        return self.sm

    def setFileInput(self, lang, str filename):
        """
            Set the input for the given file.

            :param lang: The input language (e.g. InputLanguage.SMT_LIB_2_6).
            :param filename: The input filename.
        """
        self.cip.setFileInput(<c_InputLanguage> lang.value, filename.encode())

    def setStringInput(self, lang, str input, str name):
        """
            Set the input to the given concrete string

            :param lang: The input language (e.g. InputLanguage.SMT_LIB_2_6).
            :param input: The input string.
            :param name: The name of the stream, for use in error messages.
        """
        self.cip.setStringInput(<c_InputLanguage> lang.value, input.encode(), name.encode())

    def setIncrementalStringInput(self, lang, str name):
        """
            Set that we will be feeding strings to this parser via
            appendIncrementalStringInput

            :param lang: The input language (e.g. InputLanguage.SMT_LIB_2_6).
            :param name: The name of the stream, for use in error messages.
        """
        self.cip.setIncrementalStringInput(<c_InputLanguage> lang.value, name.encode())

    def appendIncrementalStringInput(self, str input):
        """
            Append string to the input being parsed by this parser. Should be
            called after calling setIncrementalStringInput.

            :param input: The input string.
        """
        self.cip.appendIncrementalStringInput(input.encode())

    def nextCommand(self):
        """
            Parse and return the next command. Will initialize the logic to "ALL"
            or the forced logic if no logic is set prior to this point and a command
            is read that requires initializing the logic.

            :return: The parsed command. This is the null command if no command was read.
        """
        cmd = Command()
        cmd.cc = self.cip.nextCommand()
        return cmd

    def nextTerm(self):
        """
            Parse and return the next term. Requires setting the logic prior
            to this point.
        """
        return _term(self.solver.tm, self.cip.nextTerm())

    def done(self):
        """
            Is this parser done reading input?
        """
        return self.cip.done()


# ----------------------------------------------------------------------------
# Datatypes
# ----------------------------------------------------------------------------

cdef class Datatype:
    """
        A cvc5 datatype.

        Wrapper class for the C++ class :cpp:class:`cvc5::Datatype`.
    """
    cdef c_Datatype cdt
    cdef TermManager tm

    def __getitem__(self, index):
        """
            Get the datatype constructor with the given index, where index can
            be either a numeric id starting with zero, or the name of the
            constructor. In the latter case, this is a linear search through the
            constructors, so in case of multiple, similarly-named constructors,
            the first is returned.

            :param index: The id or name of the datatype constructor.
            :return: The matching datatype constructor.
        """
        if isinstance(index, int) and index >= 0:
            return _dtcons(self.tm, self.cdt[(<int?> index)])
        if isinstance(index, str):
            return _dtcons(self.tm, self.cdt[(<const string &> index.encode())])
        raise ValueError("Expecting a non-negative integer or string")

    def getConstructor(self, str name):
        """
            :param name: The name of the constructor.
            :return: A constructor by name.
        """
        return _dtcons(self.tm, self.cdt.getConstructor(name.encode()))

    def getSelector(self, str name):
        """
            :param name: The name of the selector..
            :return: A selector by name.
        """
        return _dtsel(self.tm, self.cdt.getSelector(name.encode()))

    def getName(self):
        """
            :return: The name of the datatype.
        """
        return self.cdt.getName().decode()

    def getNumConstructors(self):
        """
            :return: The number of constructors in this datatype.
        """
        return self.cdt.getNumConstructors()

    def getParameters(self):
        """
            :return: The parameters of this datatype, if it is parametric. An
                     exception is thrown if this datatype is not parametric.
        """
        param_sorts = []
        for s in self.cdt.getParameters():
            sort = _sort(self.tm, s)
            param_sorts.append(sort)
        return param_sorts

    def isParametric(self):
        """
            .. warning::

                This function is experimental and may change in future versions.

            :return: True if this datatype is parametric.
        """
        return self.cdt.isParametric()

    def isCodatatype(self):
        """
            :return: True if this datatype corresponds to a co-datatype.
        """
        return self.cdt.isCodatatype()

    def isTuple(self):
        """
            :return: True if this datatype corresponds to a tuple.
        """
        return self.cdt.isTuple()

    def isRecord(self):
        """
            .. warning::

                This function is experimental and may change in future versions.

            :return: True if this datatype corresponds to a record.
        """
        return self.cdt.isRecord()

    def isFinite(self):
        """
            :return: True if this datatype is finite.
        """
        return self.cdt.isFinite()

    def isWellFounded(self):
        """
            Determine if this datatype is well-founded.

            If this datatype is not a codatatype, this returns false if there
            are no values of this datatype that are of finite size.

            :return: True if this datatype is well-founded
        """
        return self.cdt.isWellFounded()

    def isNull(self):
        """
            :return: True if this Datatype is a null object.
        """
        return self.cdt.isNull()

    def __str__(self):
        return self.cdt.toString().decode()

    def __repr__(self):
        return self.cdt.toString().decode()

    def __iter__(self):
        """Iterate over all constructors."""
        for ci in self.cdt:
            yield _dtcons(self.tm, ci)


cdef class DatatypeConstructor:
    """
        A cvc5 datatype constructor.

        Wrapper class for :cpp:class:`cvc5::DatatypeConstructor`.
    """
    cdef c_DatatypeConstructor cdtcons
    cdef TermManager tm

    def __getitem__(self, index):
        """
            Get the datatype selector with the given index, where index can be
            either a numeric id starting with zero, or the name of the selector.
            In the latter case, this is a linear search through the selectors,
            so in case of multiple, similarly-named selectors, the first is
            returned.

            :param index: The id or name of the datatype selector.
            :return: The matching datatype selector.
        """
        if isinstance(index, int) and index >= 0:
            return _dtsel(self.tm, self.cdtcons[(<int?> index)])
        if isinstance(index, str):
            return _dtsel(
                self.tm,
                self.cdtcons[(<const string &> index.encode())])
        raise ValueError("Expecting a non-negative integer or string")

    def getName(self):
        """
            :return: The name of the constructor.
        """
        return self.cdtcons.getName().decode()

    def getTerm(self):
        """
            Get the constructor term of this datatype constructor.

            Datatype constructors are a special class of function-like terms
            whose sort is datatype constructor
            (:py:meth:`Sort.isDatatypeConstructor()`). All datatype
            constructors, including nullary ones, should be used as the first
            argument to Terms whose kind is
            :py:obj:`APPLY_CONSTRUCTOR <Kind.APPLY_CONSTRUCTOR>`.
            For example, the nil list can be constructed via
            ``TermManager.mkTerm(APPLY_CONSTRUCTOR, [nil])``, where nil is the
            Term returned by this method.

            .. note::

                This function should not be used for parametric datatypes.
                Instead, use the method
                :py:meth:`DatatypeConstructor.getInstantiatedTerm()` below.

            :return: The constructor term.
        """
        return _term(self.tm, self.cdtcons.getTerm())

    def getInstantiatedTerm(self, Sort retSort):
        """
            Get the constructor term of this datatype constructor whose
            return type is retSort. This function is intended to be used on
            constructors of parametric datatypes and can be seen as returning
            the constructor term that has been explicitly cast to the given
            sort.

            This function is required for constructors of parametric datatypes
            whose return type cannot be determined by type inference. For
            example, given:

            .. code:: smtlib

                (declare-datatype List
                    (par (T) ((nil) (cons (head T) (tail (List T))))))

            The type of nil terms must be provided by the user. In SMT version
            2.6, this is done via the syntax for qualified identifiers:

            .. code:: smtlib

                (as nil (List Int))

            This function is equivalent of applying the above, where this
            DatatypeConstructor is the one corresponding to nil, and retSort is
            ``(List Int)``.

            .. note::

                The returned constructor term ``t`` is used to construct the
                above (nullary) application of ``nil`` with
                ``TermManager.mkTerm(APPLY_CONSTRUCTOR, t)``.

            .. warning::

                This function is experimental and may change in future versions.

            :param retSort: The desired return sort of the constructor.
            :return: The constructor term.
        """
        return _term(self.tm, self.cdtcons.getInstantiatedTerm(retSort.csort))

    def getTesterTerm(self):
        """
            Get the tester term of this datatype constructor.

            Similar to constructors, testers are a class of function-like terms
            of tester sort (:py:meth:`Sort.isDatatypeTester`), and should
            be used as the first argument of Terms of kind
            :py:obj:`Kind.APPLY_TESTER`.

            :return: The tester term for this constructor.
        """
        return _term(self.tm, self.cdtcons.getTesterTerm())

    def getNumSelectors(self):
        """
            :return: The number of selecters (so far) of this Datatype
                     constructor.
        """
        return self.cdtcons.getNumSelectors()

    def getSelector(self, str name):
        """
            :param name: The name of the datatype selector.
            :return: The first datatype selector with the given name.
        """
        return _dtsel(self.tm, self.cdtcons.getSelector(name.encode()))

    def isNull(self):
        """
            :return: True if this DatatypeConstructor is a null object.
        """
        return self.cdtcons.isNull()

    def __str__(self):
        return self.cdtcons.toString().decode()

    def __repr__(self):
        return self.cdtcons.toString().decode()

    def __iter__(self):
        """Iterate over all datatype selectors."""
        for ci in self.cdtcons:
            yield _dtsel(self.tm, ci)


cdef class DatatypeConstructorDecl:
    """
        A cvc5 datatype constructor declaration. A datatype constructor
        declaration is a specification used for creating a datatype constructor.

        Wrapper class for :cpp:class:`cvc5::DatatypeConstructorDecl`.
    """
    cdef c_DatatypeConstructorDecl cdtconsdecl
    cdef TermManager tm

    def addSelector(self, str name, Sort sort):
        """
            Add datatype selector declaration.

            :param name: The name of the datatype selector declaration to add.
            :param sort: The codomain sort of the datatype selector declaration
                         to add.
        """
        self.cdtconsdecl.addSelector(name.encode(), sort.csort)

    def addSelectorSelf(self, str name):
        """
            Add datatype selector declaration whose codomain sort is the
            datatype itself.

            :param name: The name of the datatype selector declaration to add.
        """
        self.cdtconsdecl.addSelectorSelf(name.encode())

    def addSelectorUnresolved(self, str name, str unresDatatypeName):
        """
            Add datatype selector declaration whose codomain sort is an
            unresolved datatype with the given name.

            :param name: The name of the datatype selector declaration to add.
            :param unresDataypeName: The name of the unresolved datatype. The
                                     codomain of the selector will be the
                                     resolved datatype with the given name.
        """
        self.cdtconsdecl.addSelectorUnresolved(
            name.encode(), unresDatatypeName.encode())

    def isNull(self):
        """
            :return: True if this DatatypeConstructorDecl is a null object.
        """
        return self.cdtconsdecl.isNull()

    def __str__(self):
        return self.cdtconsdecl.toString().decode()

    def __repr__(self):
        return self.cdtconsdecl.toString().decode()


cdef class DatatypeDecl:
    """
        A cvc5 datatype declaration. A datatype declaration is not itself a
        datatype (see :py:class:`Datatype`), but a specification for creating a
        datatype sort.

        The interface for a datatype declaration coincides with the syntax for
        the SMT-LIB 2.6 command `declare-datatype`, or a single datatype within
        the `declare-datatypes` command.

        Datatype sorts can be constructed from :py:class:`DatatypeDecl` using
        the methods:

            - :py:meth:`Solver.mkDatatypeSort()`
            - :py:meth:`Solver.mkDatatypeSorts()`

        Wrapper class for :cpp:class:`cvc5::DatatypeDecl`.
    """
    cdef c_DatatypeDecl cdtdecl
    cdef TermManager tm

    def addConstructor(self, DatatypeConstructorDecl ctor):
        """
            Add a datatype constructor declaration.

            :param ctor: The datatype constructor declaration to add.
        """
        self.cdtdecl.addConstructor(ctor.cdtconsdecl)

    def getNumConstructors(self):
        """
            :return: The number of constructors (so far) for this datatype
                     declaration.
        """
        return self.cdtdecl.getNumConstructors()

    def isParametric(self):
        """
            .. warning::

                This function is experimental and may change in future versions.

            :return: True if this datatype declaration is parametric.
        """
        return self.cdtdecl.isParametric()

    def getName(self):
        """
            :return: The name of this datatype declaration.
        """
        return self.cdtdecl.getName().decode()

    def isNull(self):
        """
            :return: True if this DatatypeDecl is a null object.
        """
        return self.cdtdecl.isNull()

    def __str__(self):
        return self.cdtdecl.toString().decode()

    def __repr__(self):
        return self.cdtdecl.toString().decode()


cdef class DatatypeSelector:
    """
        A cvc5 datatype selector.

        Wrapper class for :cpp:class:`cvc5::DatatypeSelector`.
    """
    cdef c_DatatypeSelector cdtsel
    cdef TermManager tm

    def getName(self):
        """
            :return: The name of this datatype selector.
        """
        return self.cdtsel.getName().decode()

    def getTerm(self):
        """
            Get the selector term of this datatype selector.

            Selector terms are a class of function-like terms of selector
            sort (:py:meth:`Sort.isDatatypeSelector()`), and should be used as
            the first argument of Terms of kind
            :py:obj:`APPLY_SELECTOR <Kind.APPLY_SELECTOR>`.

            :return: The selector term of this datatype selector.
        """
        return _term(self.tm, self.cdtsel.getTerm())

    def getUpdaterTerm(self):
        """
            Get the updater term of this datatype selector.

            Similar to selectors, updater terms are a class of function-like
            terms of updater Sort (:py:meth:`Sort.isDatatypeUpdater()`), and
            should be used as the first argument of Terms of kind
            :py:obj:`APPLY_UPDATER <Kind.APPLY_UPDATER>`.

            :return: The updater term of this datatype selector.
        """
        return _term(self.tm, self.cdtsel.getUpdaterTerm())

    def getCodomainSort(self):
        """
            :return: The codomain sort of this selector.
        """
        return _sort(self.tm, self.cdtsel.getCodomainSort())

    def isNull(self):
        """
            :return: True if this DatatypeSelector is a null object.
        """
        return self.cdtsel.isNull()

    def __str__(self):
        return self.cdtsel.toString().decode()

    def __repr__(self):
        return self.cdtsel.toString().decode()


# ----------------------------------------------------------------------------
# Op
# ----------------------------------------------------------------------------

cdef class Op:
    """
        A cvc5 operator.

        An operator is a term that represents certain operators,
        instantiated with its required parameters, e.g.,
        a term of kind
        :py:obj:`BITVECTOR_EXTRACT <Kind.BITVECTOR_EXTRACT>`.

        Wrapper class for :cpp:class:`cvc5::Op`.
    """
    cdef c_Op cop
    cdef TermManager tm

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
            :return: The kind of this operator.
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
            :return: The number of indices of this op.
        """
        return self.cop.getNumIndices()

    def __getitem__(self, int i):
        """
            Get the index at position ``i``.

            :param i: The position of the index to return.
            :return: The index at position ``i``.
        """
        return _term(self.tm, self.cop[i])


# ----------------------------------------------------------------------------
# Grammar
# ----------------------------------------------------------------------------

cdef class Grammar:
    """
        A Sygus Grammar. This class can be used to define a context-free grammar
        of terms. Its interface coincides with the definition of grammars
        (``GrammarDef``) in the SyGuS IF 2.1 standard.

        Wrapper class for :cpp:class:`cvc5::Grammar`.
    """
    cdef c_Grammar  cgrammar
    cdef TermManager tm

    def __str__(self):
        return self.cgrammar.toString().decode()

    def __hash__(self):
        return cgrammarhash(self.cgrammar)

    def isNull(self):
        return self.cgrammar.isNull()

    def addRule(self, Term ntSymbol, Term rule):
        """
            Add ``rule`` to the set of rules corresponding to ``ntSymbol``.

            :param ntSymbol: The non-terminal to which the rule is added.
            :param rule: The rule to add.
        """
        self.cgrammar.addRule(ntSymbol.cterm, rule.cterm)

    def addAnyConstant(self, Term ntSymbol):
        """
            Allow ``ntSymbol`` to be an arbitrary constant.

            :param ntSymbol: The non-terminal allowed to be constant.
        """
        self.cgrammar.addAnyConstant(ntSymbol.cterm)

    def addAnyVariable(self, Term ntSymbol):
        """
            Allow ``ntSymbol`` to be any input variable to corresponding
            synth-fun/synth-inv with the same sort as ``ntSymbol``.

            :param ntSymbol: The non-terminal allowed to be any input variable.
        """
        self.cgrammar.addAnyVariable(ntSymbol.cterm)

    def addRules(self, Term ntSymbol, rules):
        """
            Add ``ntSymbol`` to the set of rules corresponding to ``ntSymbol``.

            :param ntSymbol: The non-terminal to which the rules are added.
            :param rules: The rules to add.
        """
        cdef vector[c_Term] crules
        for r in rules:
            crules.push_back((<Term?> r).cterm)
        self.cgrammar.addRules(ntSymbol.cterm, crules)

# ----------------------------------------------------------------------------
# Results
# ----------------------------------------------------------------------------

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
            :return: True if Result is empty, i.e., a nullary Result, and not
                     an actual result returned from a
                     :py:meth:`Solver.checkSat()` (and friends) query.
        """
        return self.cr.isNull()

    def isSat(self):
        """
            :return: True if query was a satisfiable
                     :py:meth:`Solver.checkSat()` or
                     :py:meth:`Solver.checkSatAssuming()` query.
        """
        return self.cr.isSat()

    def isUnsat(self):
        """
            :return: True if query was an usatisfiable
                     :py:meth:`Solver.checkSat()` or
                     :py:meth:`Solver.checkSatAssuming()` query.
        """
        return self.cr.isUnsat()

    def isUnknown(self):
        """
            :return: True if query was a :py:meth:`Solver.checkSat()` or
                     :py:meth:`Solver.checkSatAssuming()` query and cvc5 was
                     not able to determine (un)satisfiability.
        """
        return self.cr.isUnknown()

    def getUnknownExplanation(self):
        """
            :return: An explanation for an unknown query result.
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
      Encapsulation of a solver synth result.

      This is the return value of the API methods:

        - :py:meth:`Solver.checkSynth()`
        - :py:meth:`Solver.checkSynthNext()`

      which we call synthesis queries. This class indicates whether the
      synthesis query has a solution, has no solution, or is unknown.
    """
    cdef c_SynthResult cr
    def __cinit__(self):
        # gets populated by solver
        self.cr = c_SynthResult()

    def __eq__(self, SynthResult other):
        return self.cr == other.cr

    def __ne__(self, SynthResult other):
        return self.cr != other.cr

    def isNull(self):
        """
            :return: True if SynthResult is null, i.e., not a SynthResult
                     returned from a synthesis query.
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
                     In this case, it was determined that there was no solution.
        """
        return self.cr.hasNoSolution()

    def isUnknown(self):
        """
            :return: True if the result of the synthesis query could not be
                     determined.
        """
        return self.cr.isUnknown()

    def __str__(self):
        return self.cr.toString().decode()

    def __repr__(self):
        return self.cr.toString().decode()

# ----------------------------------------------------------------------------
# TermManager
# ----------------------------------------------------------------------------

cdef class TermManager:
    """
        A cvc5 term manager.

        Wrapper class for :cpp:class:`cvc5::TermManager`.
    """
    cdef c_TermManager* ctm

    def getStatistics(self):
        """
            Get a snapshot of the current state of the statistic values of
            this term manager.

            Term manager statistics are independent from any solver instance.
            The returned object is completely decoupled from the term manager
            and will not change when the solver is used again.

            :return: A snapshot of the current state of the statistic values.
        """
        res = Statistics()
        res.cstats = self.ctm.getStatistics()
        return res

    def __cinit__(self):
        self.ctm = new c_TermManager()

    def __dealloc__(self):
        del self.ctm

    def getBooleanSort(self):
        """
            :return: Sort Boolean.
        """
        return _sort(self, self.ctm.getBooleanSort())

    def getIntegerSort(self):
        """
            :return: Sort Integer.
        """
        return _sort(self, self.ctm.getIntegerSort())

    def getRealSort(self):
        """
            :return: Sort Real.
        """
        return _sort(self, self.ctm.getRealSort())

    def getRegExpSort(self):
        """
            :return: The sort of regular expressions.
        """
        return _sort(self, self.ctm.getRegExpSort())

    def getRoundingModeSort(self):
        """
            :return: Sort RoundingMode.
        """
        return _sort(self, self.ctm.getRoundingModeSort())

    def getStringSort(self):
        """
            :return: Sort String.
        """
        return  _sort(self, self.ctm.getStringSort())

    def mkArraySort(self, Sort indexSort, Sort elemSort):
        """
            Create an array sort.

            :param indexSort: The array index sort.
            :param elemSort: The array element sort.
            :return: The array sort.
        """
        return _sort(
            self, self.ctm.mkArraySort(indexSort.csort, elemSort.csort))

    def mkBitVectorSort(self, uint32_t size):
        """
            Create a bit-vector sort.

            :param size: The bit-width of the bit-vector sort
            :return: The bit-vector sort
        """
        return _sort(self, self.ctm.mkBitVectorSort(size))

    def mkFloatingPointSort(self, uint32_t exp, uint32_t sig):
        """
            Create a floating-point sort.

            :param exp: The bit-width of the exponent of the floating-point
                        sort.
            :param sig: The bit-width of the significand of the floating-point
                        sort.
        """
        return _sort(self, self.ctm.mkFloatingPointSort(exp, sig))

    def mkFiniteFieldSort(self, size, int base=10):
        """
            Create a finite field sort.

            Supports the following arguments:

            - ``Sort mkFiniteFieldSort(int size)``
            - ``Sort mkFiniteFieldSort(string size)``
            - ``Sort mkFiniteFieldSort(string size, int base)``

            :param size: The size of the field. Must be a prime-power.
                         An integer or string of base 10 if the base is not
                         explicitly given, and else a string in the given base.
            :param base: The base of the string representation of ``size``.
        """
        if base == 10:
            if not isinstance(size, str) and not isinstance(size, int):
                raise ValueError(
                    "Invalid first argument '{}' to mkFiniteFieldSort, "
                    "expected string or integer value".format(size))
        else:
            if not isinstance(size, str):
                raise ValueError(
                    "Invalid first argument '{}' to mkFiniteFieldSort, "
                    "expected string value".format(size))
        if not isinstance(base, int):
            raise ValueError(
            "Invalid second argument '{}' to mkFiniteFieldSort, "
            "expected integer value".format(base))
        return _sort(
            self,
            self.ctm.mkFiniteFieldSort(
              <const string&> str(size).encode(), <uint32_t> base))

    def mkDatatypeSort(self, DatatypeDecl dtypedecl):
        """
            Create a datatype sort.

            :param dtypedecl: The datatype declaration from which the sort is
                              created.
            :return: The datatype sort.
        """
        return _sort(self, self.ctm.mkDatatypeSort(dtypedecl.cdtdecl))

    def mkDatatypeSorts(self, list dtypedecls):
        """
            Create a vector of datatype sorts using unresolved sorts. The names
            of the datatype declarations in dtypedecls must be distinct.

            When constructing datatypes, unresolved sorts are replaced by the
            datatype sort constructed for the datatype declaration it is
            associated with.

            :param dtypedecls: The datatype declarations from which the sort is
                               created.
            :return: The datatype sorts.
        """
        sorts = []
        cdef vector[c_DatatypeDecl] decls
        for decl in dtypedecls:
            decls.push_back((<DatatypeDecl?> decl).cdtdecl)
        csorts = self.ctm.mkDatatypeSorts(
            <const vector[c_DatatypeDecl]&> decls)
        for csort in csorts:
          sorts.append(_sort(self, csort))
        return sorts

    def mkFunctionSort(self, sorts, Sort codomain):
        """
            Create function sort.

            :param sorts: The sort of the function arguments.
            :param codomain: The sort of the function return value.
            :return: The function sort.
        """
        # populate a vector with dereferenced c_Sorts
        cdef vector[c_Sort] v
        if isinstance(sorts, Sort):
            v.push_back((<Sort?>sorts).csort)
        else:
            for s in sorts:
                v.push_back((<Sort?>s).csort)

        return _sort(
            self,
            self.ctm.mkFunctionSort(<const vector[c_Sort]&> v, codomain.csort))

    def mkParamSort(self, str symbolname = None):
        """
            Create a sort parameter.

            .. warning::

                This function is experimental and may change in future versions.

            :param symbol: The name of the sort.
            :return: The sort parameter.
        """
        if symbolname is None:
          return _sort(self, self.ctm.mkParamSort())
        return _sort(self, self.ctm.mkParamSort(symbolname.encode()))

    def mkSkolem(self, id, *indices):
        """
            Create a skolem.

            .. warning::

                This function is experimental and may change in future versions.

            :param id: The skolem id.
            :param indices: The indices for the skolem.
            :return: The skolem with the given id and indices.
        """
        cdef vector[c_Term] v
        for t in indices:
            v.push_back((<Term?> t).cterm)
        return _term(self, self.ctm.mkSkolem(<c_SkolemId> id.value, v))

    def getNumIndicesForSkolemId(self, id):
        """
            Get the number of indices for a skolem id.

            .. warning::

                This function is experimental and may change in future versions.

            :param id: The skolem id.
            :return: The number of indice for a skolem with the given id.
        """
        return self.ctm.getNumIndicesForSkolemId(<c_SkolemId> id.value)

    def mkPredicateSort(self, *sorts):
        """
            Create a predicate sort.

            :param sorts: The list of sorts of the predicate.
            :return: The predicate sort.
        """
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        return _sort(self, self.ctm.mkPredicateSort(<const vector[c_Sort]&> v))

    def mkRecordSort(self, *fields):
        """
            Create a record sort

            .. warning::

                This function is experimental and may change in future versions.

            :param fields: The list of fields of the record.
            :return: The record sort.
        """
        cdef vector[pair[string, c_Sort]] v
        cdef pair[string, c_Sort] p
        for f in fields:
            name, sortarg = f
            name = name.encode()
            p = pair[string, c_Sort](<string?> name, (<Sort?> sortarg).csort)
            v.push_back(p)
        return _sort(
            self,
            self.ctm.mkRecordSort(<const vector[pair[string, c_Sort]] &> v))

    def mkSetSort(self, Sort elemSort):
        """
            Create a set sort.

            :param elemSort: The sort of the set elements.
            :return: The set sort.
        """
        return _sort(self, self.ctm.mkSetSort(elemSort.csort))

    def mkBagSort(self, Sort elemSort):
        """
            Create a bag sort.

            :param elemSort: The sort of the bag elements.
            :return: The bag sort.
        """
        return _sort(self, self.ctm.mkBagSort(elemSort.csort))

    def mkSequenceSort(self, Sort elemSort):
        """
            Create a sequence sort.

            :param elemSort: The sort of the sequence elements
            :return: The sequence sort.
        """
        return _sort(self, self.ctm.mkSequenceSort(elemSort.csort))

    def mkAbstractSort(self, kind):
        """
            Create an abstract sort. An abstract sort represents a sort for a
            given kind whose parameters and arguments are unspecified.

            Given ``kind`` must be the kind of a sort that can be abstracted,
            i.e., a sort that has indices or argument sorts. For example,
            :py:obj:`ARRAY_SORT <Kind.ARRAY_SORT>`
            and :py:obj:`BITVECTOR_SORT <Kind.BITVECTOR_SORT>` can be
            passed as the kind ``k`` to this method, while
            :py:obj:`INTEGER_SORT <Kind.INTEGER_SORT>` and
            :py:obj:`STRING_SORT <Kind.STRING_SORT>` cannot.

            .. note::
                Providing the kind :py:obj:`ABSTRACT_SORT <Kind.ABSTRACT_SORT>`
                as an argument to this method returns the (fully) unspecified
                sort, denoted ``?``.

            .. note::
                Providing a kind of sort that has no indices and a fixed arity
                of argument sorts will return the sort of kind ``kind`` whose
                arguments are the unspecified sort. For example,
                ``mkAbstractSort(ARRAY_SORT)`` will return the sort
                ``(ARRAY_SORT ? ?)`` instead of the abstract sort whose
                abstract kind is py:obj:`ARRAY_SORT <Kind.ARRAY_SORT>`.

            :param k: The kind of the abstract sort
            :return: The abstract sort.

            .. warning::

                This function is experimental and may change in future versions.
        """
        return _sort(self, self.ctm.mkAbstractSort(<c_SortKind> kind.value))

    def mkUninterpretedSort(self, str name = None):
        """
            Create an uninterpreted sort.

            :param symbol: The name of the sort.
            :return: The uninterpreted sort.
        """
        cdef Sort sort = Sort(self)
        if name is None:
          return _sort(self, self.ctm.mkUninterpretedSort())
        return _sort(self, self.ctm.mkUninterpretedSort(name.encode()))

    def mkUnresolvedDatatypeSort(self, str name, size_t arity = 0):
        """
            Create an unresolved datatype sort.

            This is for creating yet unresolved sort placeholders for mutually
            recursive datatypes.

            :param symbol: The name of the sort.
            :param arity: The number of sort parameters of the sort.
            :return: The unresolved sort.
        """
        return _sort(
            self,
            self.ctm.mkUnresolvedDatatypeSort(name.encode(), arity))

    def mkUninterpretedSortConstructorSort(self, size_t arity, str symbol = None):
        """
            Create a sort constructor sort.

            An uninterpreted sort constructor is an uninterpreted sort with
            arity > 0.

            :param symbol: The symbol of the sort.
            :param arity: The arity of the sort (must be > 0).
            :return: The sort constructor sort.
        """
        cdef Sort sort = Sort(self)
        if symbol is None:
          return _sort(self, self.ctm.mkUninterpretedSortConstructorSort(arity))
        return _sort(
            self,
            self.ctm.mkUninterpretedSortConstructorSort(arity, symbol.encode()))

    def mkTupleSort(self, *sorts):
        """
            Create a tuple sort.

            :param sorts: Of the elements of the tuple.
            :return: The tuple sort.
        """
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        return _sort(self, self.ctm.mkTupleSort(v))

    def mkNullableSort(self, Sort elemSort):
        """
            Create a nullable sort.

            :param elemSort: The sort of the element of the nullable.
            :return: The nullable sort.
        """
        return _sort(self, self.ctm.mkNullableSort(elemSort.csort))

    def mkTerm(self, kind_or_op, *args):
        """
            Create a term.

            Supports the following arguments:

            - ``Term mkTerm(Kind kind)``
            - ``Term mkTerm(Op op)``
            - ``Term mkTerm(Kind kind, *args)``
            - ``Term mkTerm(Op op, *args)``

            where ``*args`` is a comma-separated list of terms.
        """
        cdef vector[c_Term] v
        op = kind_or_op
        if isinstance(kind_or_op, Kind):
            op = self.mkOp(kind_or_op)
        if len(args) == 0:
            return _term(self, self.ctm.mkTerm((<Op?> op).cop))
        for a in args:
            v.push_back((<Term?> a).cterm)
        return _term(self, self.ctm.mkTerm((<Op?> op).cop, v))

    def mkTuple(self, terms):
        """
            Create a tuple term. Terms are automatically converted if sorts are
            compatible.

            :param terms: The elements in the tuple.
            :return: The tuple Term.
        """
        cdef vector[c_Term] cterms

        for s in terms:
            cterms.push_back((<Term?> s).cterm)
        return _term(self, self.ctm.mkTuple(cterms))

    def mkNullableSome(self, Term term):
        """
            Create a nullable some term.

            :param term: The elements value.
            :return: The element value wrapped in some constructor.
        """
        return _term(self, self.ctm.mkNullableSome(term.cterm))

    def mkNullableVal(self, Term term):
        """
            Create a selector for nullable term.

            :param term: A nullable term.
            :return: The element value of the nullable term.
        """
        return _term(self, self.ctm.mkNullableVal(term.cterm))

    def mkNullableIsNull(self, Term term):
        """
            Create a null tester for a nullable term.

            :param term: A nullable term.
            :return: A tester whether term is null.
        """
        return _term(self, self.ctm.mkNullableIsNull(term.cterm))

    def mkNullableIsSome(self, Term term):
        """
            Create a some tester for a nullable term.

            :param term: A nullable term.
            :return: A tester whether term is some.
        """
        return _term(self, self.ctm.mkNullableIsSome(term.cterm))

    def mkNullableNull(self, Sort sort):
        """
            Create a constant representing an null of the given sort.

            :param term: The sort of the Nullable element.
            :return: The null constant.
        """
        return _term(self, self.ctm.mkNullableNull(sort.csort))

    def mkNullableLift(self, kind, *args):
        """
            Create a term that lifts kind to nullable terms.
            Example:
            If we have the term ((_ nullable.lift +) x y),
            where x, y of type (Nullable Int), then
            kind would be ADD, and args would be [x, y].
            This function would return
            (nullable.lift (lambda ((a Int) (b Int)) (+ a b)) x y)

            :param kind: The lifted operator.
            :param args: The arguments of the lifted operator.
            :return: A term of Kind NULLABLE_LIFT where the first child
                     is a lambda expression, and the remaining children are
                     the original arguments.
        """
        cdef vector[c_Term] cterms
        for a in args:
            cterms.push_back((<Term?> a).cterm)
        return _term(self, self.ctm.mkNullableLift(<c_Kind> kind.value, cterms))

    def mkOp(self, k, *args):
        """
            Create operator.

            Supports the following arguments:

            - ``Op mkOp(Kind kind)``
            - ``Op mkOp(Kind kind, const string& arg)``
            - ``Op mkOp(Kind kind, uint32_t arg0, ...)``
        """
        cdef vector[uint32_t] v

        if len(args) == 0:
            return _op(self, self.ctm.mkOp(<c_Kind> k.value))
        elif len(args) == 1 and isinstance(args[0], str):
            return _op(
                self,
                self.ctm.mkOp(
                  <c_Kind> k.value, <const string &> args[0].encode()))
        for a in args:
            if not isinstance(a, int):
              raise ValueError(
                        "Expected uint32_t for argument {}".format(a))
            if a < 0 or a >= 2 ** 31:
                raise ValueError(
                        "Argument {} must fit in a uint32_t".format(a))
            v.push_back(<uint32_t?> a)
        return _op(self, self.ctm.mkOp(<c_Kind> k.value, v))

    def mkTrue(self):
        """
            Create a Boolean true constant.

            :return: The true constant.
        """
        return _term(self, self.ctm.mkTrue())

    def mkFalse(self):
        """
            Create a Boolean false constant.

            :return: The false constant.
        """
        return _term(self, self.ctm.mkFalse())

    def mkBoolean(self, bint val):
        """
            Create a Boolean constant.

            :return: The Boolean constant.
            :param val: The value of the constant.
        """
        return _term(self, self.ctm.mkBoolean(val))

    def mkPi(self):
        """
            Create a constant representing the number Pi.

            :return: A constant representing :py:obj:`PI <Kind.PI>`.
        """
        return _term(self, self.ctm.mkPi())

    def mkInteger(self, val):
        """
            Create an integer constant.

            :param val: Representation of the constant: either a string or
                        integer.
            :return: A constant of sort Integer.
        """
        if isinstance(val, str):
            return _term(
                self,
                self.ctm.mkInteger(<const string &> str(val).encode()))
        assert(isinstance(val, int))
        return _term(self, self.ctm.mkInteger(<int?> val))

    def mkReal(self, numerator, denominator=None):
        """
            Create a real constant from a numerator and an optional denominator.

            First converts the arguments to a temporary string, either
            ``"<numerator>"`` or ``"<numerator>/<denominator>"``. This temporary
            string is forwarded to :cpp:func:`cvc5::TermManager::mkReal()` and should
            thus represent an integer, a decimal number or a fraction.

            :param numerator: The numerator.
            :param denominator: The denominator, or ``None``.
            :return: A real term with literal value.
        """
        if denominator is None:
            return _term(self, self.ctm.mkReal(str(numerator).encode()))
        return _term(
            self,
            self.ctm.mkReal("{}/{}".format(numerator, denominator).encode()))

    def mkRegexpAll(self):
        """
            Create a regular expression all (``re.all``) term.

            :return: The all term.
        """
        return _term(self, self.ctm.mkRegexpAll())

    def mkRegexpAllchar(self):
        """
            Create a regular expression allchar (``re.allchar``) term.

            :return: The allchar term.
        """
        return _term(self, self.ctm.mkRegexpAllchar())

    def mkRegexpNone(self):
        """
            Create a regular expression none (``re.none``) term.

            :return: The none term.
        """
        return _term(self, self.ctm.mkRegexpNone())

    def mkEmptySet(self, Sort s):
        """
            Create a constant representing an empty set of the given sort.

            :param sort: The sort of the set elements.
            :return: The empty set constant.
        """
        return _term(self, self.ctm.mkEmptySet(s.csort))

    def mkEmptyBag(self, Sort s):
        """
            Create a constant representing an empty bag of the given sort.

            :param sort: The sort of the bag elements.
            :return: The empty bag constant.
        """
        return _term(self, self.ctm.mkEmptyBag(s.csort))

    def mkSepEmp(self):
        """
            Create a separation logic empty term.

            .. warning::

                This function is experimental and may change in future versions.

            :return: The separation logic empty term.
        """
        return _term(self, self.ctm.mkSepEmp())

    def mkSepNil(self, Sort sort):
        """
            Create a separation logic nil term.

            .. warning::

                This function is experimental and may change in future versions.

            :param sort: The sort of the nil term.
            :return: The separation logic nil term.
        """
        return _term(self, self.ctm.mkSepNil(sort.csort))

    def mkString(self, str s, useEscSequences = None):
        """
            Create a String constant from a ``str`` which may contain SMT-LIB
            compatible escape sequences like ``\\u1234`` to encode unicode
            characters.

            :param s: The string this constant represents.
            :param useEscSequences: Determines whether escape sequences in `s`
                                    should be converted to the corresponding
                                    unicode character
            :return: The String constant.
        """
        if isinstance(useEscSequences, bool):
            return _term(
                self,
                self.ctm.mkString(s.encode(), <bint> useEscSequences))

        cdef Py_ssize_t n = len(s)
        cdef int kind = PyUnicode_KIND(s)
        cdef void* data = PyUnicode_DATA(s)
        cdef Py_ssize_t i

        cdef c_u32string result
        result.resize(n)

        for i in range(n):
            result[i] = <Py_UCS4>PyUnicode_READ(kind, data, i)

        return _term(self, self.ctm.mkString(result))

    def mkEmptySequence(self, Sort sort):
        """
            Create an empty sequence of the given element sort.

            :param sort: The element sort of the sequence.
            :return: The empty sequence with given element sort.
        """
        return _term(self, self.ctm.mkEmptySequence(sort.csort))

    def mkUniverseSet(self, Sort sort):
        """
            Create a universe set of the given sort.

            :param sort: The sort of the set elements
            :return: The universe set constant
        """
        return _term(self, self.ctm.mkUniverseSet(sort.csort))

    def mkBitVector(self, int size, *args):
        """
            Create bit-vector value.

            Supports the following arguments:

            - ``Term mkBitVector(int size, int val=0)``
            - ``Term mkBitVector(int size, string val, int base)``

            :param size: The bit-width.
            :param val: An integer representating the value, in the first form.
                        In the second form, a string representing the value.
            :param base: The base of the string representation (second form
                         only).
            :return: A Term representing a bit-vector value.
        """
        if len(args) == 0:
            return _term(self, self.ctm.mkBitVector(<uint32_t> size))
        if len(args) == 1:
            val = args[0]
            if not isinstance(val, int):
                raise ValueError(
                    "Invalid second argument to mkBitVector '{}', "
                    "expected integer value".format(size))
            return _term(
                self,
                self.ctm.mkBitVector(
                  <uint32_t> size, <const string&> str(val).encode(), 10))
        if len(args) == 2:
            val = args[0]
            base = args[1]
            if not isinstance(val, str):
                raise ValueError(
                    "Invalid second argument to mkBitVector '{}', "
                    "expected value string".format(size))
            if not isinstance(base, int):
                raise ValueError(
                    "Invalid third argument to mkBitVector '{}', "
                    "expected base given as integer".format(size))
            return _term(
                self,
                self.ctm.mkBitVector(
                  <uint32_t> size,
                  <const string&> str(val).encode(),
                  <uint32_t> base))
        raise ValueError("Unexpected inputs to mkBitVector")

    def mkFiniteFieldElem(self, value, Sort sort, int base=10):
        """
            Create finite field value.

            Supports the following arguments:

            - ``Term mkFiniteFieldElem(int value, Sort sort)``
            - ``Term mkFiniteFieldElem(string value, Sort sort)``
            - ``Term mkFiniteFieldElem(string value, Sort sort, int base)``

            :param value: The value of the element's integer representation.
                          An integer or string of base 10 if the base is not
                          explicitly given, and else a string in the given base.
            :param sort: The field to create the element in.
            :param base: The base of the string representation of ``value``.
            :return: A Term representing a finite field value.
        """
        if base == 10:
            if not isinstance(value, str) and not isinstance(value, int):
                raise ValueError(
                    "Invalid first argument to mkFiniteFieldElem '{}', "
                    "expected string or integer value".format(value))
        else:
            if not isinstance(value, str):
                raise ValueError(
                    "Invalid first argument to mkFiniteFieldElem '{}', "
                    "expected string value".format(value))

        if not isinstance(base, int):
            raise ValueError(
            "Invalid third argument to mkFiniteFieldElem '{}', "
            "expected integer value".format(base))

        return _term(
            self,
            self.ctm.mkFiniteFieldElem(
              <const string&> str(value).encode(),
              sort.csort,
              <uint32_t> base))

    def mkConstArray(self, Sort sort, Term val):
        """
            Create a constant array with the provided constant value stored at
            every index

            :param sort: The sort of the constant array (must be an array sort).
            :param val: The constant value to store (must match the sort's
                        element sort).
            :return: The constant array term.
            """
        return _term(self, self.ctm.mkConstArray(sort.csort, val.cterm))

    def mkFloatingPointPosInf(self, int exp, int sig):
        """
            Create a positive infinity floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.
        """
        return _term(self, self.ctm.mkFloatingPointPosInf(exp, sig))

    def mkFloatingPointNegInf(self, int exp, int sig):
        """
            Create a negative infinity floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.
        """
        return _term(self, self.ctm.mkFloatingPointNegInf(exp, sig))

    def mkFloatingPointNaN(self, int exp, int sig):
        """
            Create a not-a-number (NaN) floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.
        """
        return _term(self, self.ctm.mkFloatingPointNaN(exp, sig))

    def mkFloatingPointPosZero(self, int exp, int sig):
        """
            Create a positive zero (+0.0) floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.
        """
        return _term(self, self.ctm.mkFloatingPointPosZero(exp, sig))

    def mkFloatingPointNegZero(self, int exp, int sig):
        """
            Create a negative zero (+0.0) floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.
        """
        return _term(self, self.ctm.mkFloatingPointNegZero(exp, sig))

    def mkRoundingMode(self, rm):
        """
            Create a roundingmode constant.

            :param rm: The floating point rounding mode this constant
                       represents.
        """
        return _term(self, self.ctm.mkRoundingMode(<c_RoundingMode> rm.value))

    def mkFloatingPoint(self, arg0, arg1, Term arg2):
        """
            Create a floating-point value from a bit-vector given in IEEE-754
            format, or from its three IEEE-754 bit-vector value components
            (sign bit, exponent, significand). Arguments must be either given
            as (int, int, Term) or (Term, Term, Term).

            :param arg0: The size of the exponent or the sign bit.
            :param arg1: The size of the signifcand or the bit-vector
                         representing the exponent.
            :param arg2: The value of the floating-point constant as a
                         bit-vector term or the bit-vector representing the
                         significand.
            :return: The floating-point value.
        """
        if isinstance(arg0, int):
            return _term(
                self,
                self.ctm.mkFloatingPoint(<int> arg0, <int> arg1, arg2.cterm))
        return _term(
            self,
            self.ctm.mkFloatingPoint(
                (<Term> arg0).cterm, (<Term> arg1).cterm, arg2.cterm))

    def mkCardinalityConstraint(self, Sort sort, int index):
        """
            Create cardinality constraint.

            .. warning::

                This function is experimental and may change in future versions.

            :param sort: Sort of the constraint.
            :param index: The upper bound for the cardinality of the sort.
        """
        return _term(self, self.ctm.mkCardinalityConstraint(sort.csort, index))

    def mkConst(self, Sort sort, symbol=None):
        """
            Create (first-order) constant (0-arity function symbol).

            SMT-LIB:

            .. code-block:: smtlib

                ( declare-const <symbol> <sort> )
                ( declare-fun <symbol> ( ) <sort> )

            :param sort: The sort of the constant.
            :param symbol: The name of the constant. If None, a default symbol
                           is used.
            :return: The first-order constant.
        """
        if symbol is None:
            return _term(self, self.ctm.mkConst(sort.csort))
        return _term(
            self,
            self.ctm.mkConst(sort.csort, (<str?> symbol).encode()))

    def mkVar(self, Sort sort, symbol=None):
        """
            Create a bound variable to be used in a binder (i.e. a quantifier,
            a lambda, or a witness binder).

            :param sort: The sort of the variable.
            :param symbol: The name of the variable.
            :return: The variable.
        """
        if symbol is None:
            return _term(self, self.ctm.mkVar(sort.csort))
        return _term(
            self,
            self.ctm.mkVar(sort.csort, (<str?> symbol).encode()))

    def mkDatatypeConstructorDecl(self, str name):
        """
            Create datatype constructor declaration.

            :param name: The name of the constructor.
            :return: The datatype constructor declaration.
        """
        return _dtconsdecl(
            self, self.ctm.mkDatatypeConstructorDecl(name.encode()))

    def mkDatatypeDecl(self, str name, sorts_or_bool=None, isCoDatatype=None):
        """
            Create a datatype declaration.

            :param name: The name of the datatype.
            :param isCoDatatype: True if a codatatype is to be constructed.
            :return: The datatype declaration.
        """
        cdef vector[c_Sort] v

        # argument cases
        if sorts_or_bool is None and isCoDatatype is None:
            return _dtdecl(self, self.ctm.mkDatatypeDecl(name.encode()))
        if sorts_or_bool is not None and isCoDatatype is None:
            if isinstance(sorts_or_bool, bool):
                return _dtdecl(
                    self,
                    self.ctm.mkDatatypeDecl(
                        <const string &> name.encode(), <bint> sorts_or_bool))
            if isinstance(sorts_or_bool, list):
                for s in sorts_or_bool:
                    v.push_back((<Sort?> s).csort)
                return _dtdecl(
                    self,
                    self.ctm.mkDatatypeDecl(
                        <const string &> name.encode(),
                        <const vector[c_Sort]&> v))
            raise ValueError("Unhandled second argument type {}"
                                 .format(type(sorts_or_bool)))
        if sorts_or_bool is not None and isCoDatatype is not None:
            if isinstance(sorts_or_bool, list):
                for s in sorts_or_bool:
                    v.push_back((<Sort?> s).csort)
                return _dtdecl(
                    self,
                    self.ctm.mkDatatypeDecl(
                        <const string &> name.encode(),
                        <const vector[c_Sort]&> v,
                        <bint> isCoDatatype))
            raise ValueError("Unhandled second argument type {}"
                                 .format(type(sorts_or_bool)))
        raise ValueError("Can't create DatatypeDecl with {}".format(
                    [type(a) for a in [name, sorts_or_bool, isCoDatatype]]))

# ----------------------------------------------------------------------------
# Plugin
# ----------------------------------------------------------------------------

cdef class Plugin:
    """
        A cvc5 plugin.

        Wrapper class for :cpp:class:`cvc5::Plugin`.
    """
    cdef c_PyPlugin* cplugin
    cdef TermManager tm

    # Ensure that both __init__ and __cinit__ have the same signature
    def __init__(self, TermManager tm):
        pass

    def __cinit__(self, TermManager tm):
        self.tm = tm
        self.cplugin = new c_PyPlugin(<cpy_ref.PyObject*>self, dereference(tm.ctm))

    def __dealloc__(self):
        del self.cplugin

    def __term_manager(self):
        return self.tm

    def check(self):
        """
            Call to check, return list of lemmas to add to the SAT solver.
            This method is called periodically, roughly at every SAT decision.

            :return: The list of lemmas to add to the SAT solver.
        """
        lemmas = []
        for l in self.cplugin.plugin_check():
            lemmas.append(_term(self.tm, l))
        return lemmas

    def notifySatClause(self, Term cl):
        """
            Notify SAT clause, called when cl is a clause learned by the SAT
            solver.

            :param cl: The learned clause.
        """
        self.cplugin.plugin_notifySatClause(cl.cterm)

    def notifyTheoryLemma(self, Term lem):
        """
            Notify theory lemma, called when lem is a theory lemma sent by a
            theory solver.

            :param lem: The theory lemma.
        """
        self.cplugin.plugin_notifyTheoryLemma(lem.cterm)

    def getName(self):
        """
            Get the name of the plugin (for debugging).

            :return: The name of the plugin.
        """
        raise NotImplementedError


# ----------------------------------------------------------------------------
# Solver
# ----------------------------------------------------------------------------

cdef class Solver:
    """
        A cvc5 solver.

        Wrapper class for :cpp:class:`cvc5::Solver`.
    """
    cdef c_Solver* csolver
    cdef TermManager tm

    def __cinit__(self, TermManager tm = None):
        if not tm:
          self.tm = TermManager()
        else:
          self.tm = tm
        self.csolver = new c_Solver(dereference(self.tm.ctm))

    def __dealloc__(self):
        del self.csolver

    def getTermManager(self):
        """
            Get the associated term manager instance.
            :return: The term manager instance.
        """
        return self.tm

    def getBooleanSort(self):
        """
            Get the Boolean sort.
            :return: Sort Boolean.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.getBooleanSort()

    def getIntegerSort(self):
        """
            Get the integer sort.
            :return: Sort Integer.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.getIntegerSort()

    def getRealSort(self):
        """
            Get the real sort.
            :return: Sort Real.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.getRealSort()

    def getRegExpSort(self):
        """
            Get the regular expression sort.
            :return: The sort of regular expressions.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.getRegExpSort()

    def getRoundingModeSort(self):
        """
            Get the rounding mode sort.
            :return: Sort RoundingMode.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.getRoundingModeSort()

    def getStringSort(self):
        """
            :return: Sort String.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.getStringSort()

    def mkArraySort(self, Sort indexSort, Sort elemSort):
        """
            Create an array sort.

            :param indexSort: The array index sort.
            :param elemSort: The array element sort.
            :return: The array sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkArraySort(indexSort, elemSort)

    def mkBitVectorSort(self, uint32_t size):
        """
            Create a bit-vector sort.

            :param size: The bit-width of the bit-vector sort
            :return: The bit-vector sort

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkBitVectorSort(size)

    def mkFloatingPointSort(self, uint32_t exp, uint32_t sig):
        """
            Create a floating-point sort.

            :param exp: The bit-width of the exponent of the floating-point
                        sort.
            :param sig: The bit-width of the significand of the floating-point
                        sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPointSort(exp, sig)

    def mkFiniteFieldSort(self, size, int base=10):
        """
            Create a finite field sort.

            Supports the following arguments:

            - ``Sort mkFiniteFieldSort(int size)``
            - ``Sort mkFiniteFieldSort(string size)``
            - ``Sort mkFiniteFieldSort(string size, int base)``

            :param size: The size of the field. Must be a prime-power.
                         An integer or string of base 10 if the base is not
                         explicitly given, and else a string in the given base.
            :param base: The base of the string representation of ``size``.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFiniteFieldSort(size, base)

    def mkDatatypeSort(self, DatatypeDecl dtypedecl):
        """
            Create a datatype sort.

            :param dtypedecl: The datatype declaration from which the sort is
                              created.
            :return: The datatype sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkDatatypeSort(dtypedecl)

    def mkDatatypeSorts(self, list dtypedecls):
        """
            Create a vector of datatype sorts using unresolved sorts. The names
            of the datatype declarations in dtypedecls must be distinct.

            When constructing datatypes, unresolved sorts are replaced by the
            datatype sort constructed for the datatype declaration it is
            associated with.

            :param dtypedecls: The datatype declarations from which the sort is
                               created.
            :return: The datatype sorts.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkDatatypeSorts(dtypedecls)

    def mkFunctionSort(self, sorts, Sort codomain):
        """
            Create function sort.

            :param sorts: The sort of the function arguments.
            :param codomain: The sort of the function return value.
            :return: The function sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFunctionSort(sorts, codomain)

    def mkParamSort(self, str symbolname = None):
        """
            Create a sort parameter.

            :param symbol: The name of the sort.
            :return: The sort parameter.

            .. warning::

                This function is experimental and may change in future versions.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkParamSort(symbolname)

    def mkSkolem(self, id, *indices):
        """
            Create a skolem.

            :param id: The skolem id.
            :param indices: The indices for the skolem.
            :return: The skolem with the given id and indices.
        """
        return self.tm.mkSkolem(id, indices)

    def getNumIndicesForSkolemId(self, id):
        """
            Get the number of indices for a skolem id.

            :param id: The skolem id.
            :return: The number of indice for a skolem with the given id.
        """
        return self.tm.getNumIndicesForSkolemId(id)

    def mkPredicateSort(self, *sorts):
        """
            Create a predicate sort.

            :param sorts: The list of sorts of the predicate.
            :return: The predicate sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkPredicateSort(sorts)

    def mkRecordSort(self, *fields):
        """
            Create a record sort

            :param fields: The list of fields of the record.
            :return: The record sort.
            :note: This function is deprecated and will be removed in a future
                   release.

            .. warning::

                This function is experimental and may change in future versions.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkRecordSort(fields)

    def mkSetSort(self, Sort elemSort):
        """
            Create a set sort.

            :param elemSort: The sort of the set elements.
            :return: The set sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkSetSort(elemSort)

    def mkBagSort(self, Sort elemSort):
        """
            Create a bag sort.

            :param elemSort: The sort of the bag elements.
            :return: The bag sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkBagSort(elemSort)

    def mkSequenceSort(self, Sort elemSort):
        """
            Create a sequence sort.

            :param elemSort: The sort of the sequence elements
            :return: The sequence sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkSequenceSort(elemSort)

    def mkAbstractSort(self, kind):
        """
            Create an abstract sort. An abstract sort represents a sort for a
            given kind whose parameters and arguments are unspecified.

            Parameter ``kind`` must be the kind of a sort that can be
            abstracted, i.e., a sort that has indices or argument sorts. For
            example, :py:obj:`ARRAY_SORT<Kind.ARRAY_SORT>` and
            :py:obj:`BITVECTOR_SORT <Kind.BITVECTOR_SORT>` can be passed as the
            to this function, while
            :py:obj:`INTEGER_SORT <Kind.INTEGER_SORT>` and
            :py:obj:`STRING_SORT <Kind.STRING_SORT>` cannot.

            .. note::
                Providing the kind :py:obj:`ABSTRACT_SORT <Kind.ABSTRACT_SORT>`
                as an argument to this method returns the (fully) unspecified
                sort, denoted ``?``.

            .. note::
                Providing a kind of sort that has no indices and a fixed arity
                of argument sorts will return the sort of ``kind`` whose
                arguments are the unspecified sort. For example,
                ``mkAbstractSort(ARRAY_SORT)`` will return the sort
                ``(ARRAY_SORT ? ?)`` instead of the abstract sort whose
                abstract kind is py:obj:`ARRAY_SORT <Kind.ARRAY_SORT>`.

            :param k: The kind of the abstract sort
            :return: The abstract sort.

            .. warning::

                This function is experimental and may change in future versions.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkAbstractSort(kind)

    def mkUninterpretedSort(self, str name = None):
        """
            Create an uninterpreted sort.

            :param symbol: The name of the sort.
            :return: The uninterpreted sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkUninterpretedSort(name)

    def mkUnresolvedDatatypeSort(self, str name, size_t arity = 0):
        """
            Create an unresolved datatype sort.

            This is for creating yet unresolved sort placeholders for mutually
            recursive datatypes.

            :param symbol: The name of the sort.
            :param arity: The number of sort parameters of the sort.
            :return: The unresolved sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkUnresolvedDatatypeSort(name, arity)

    def mkUninterpretedSortConstructorSort(self, size_t arity, str symbol = None):
        """
            Create a sort constructor sort.

            An uninterpreted sort constructor is an uninterpreted sort with
            arity > 0.

            :param symbol: The symbol of the sort.
            :param arity: The arity of the sort (must be > 0).
            :return: The sort constructor sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkUninterpretedSortConstructorSort(arity, symbol)

    def mkTupleSort(self, *sorts):
        """
            Create a tuple sort.

            :param sorts: Of the elements of the tuple.
            :return: The tuple sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkTupleSort(sorts)

    def mkNullableSort(self, Sort elemSort):
        """
            Create a nullable sort.

            :param elemSort: The sort of the element of the nullable.
            :return: The nullable sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableSort(elemSort)

    def mkTerm(self, kind_or_op, *args):
        """
            Create a term.

            Supports the following arguments:

            - ``Term mkTerm(Kind kind)``
            - ``Term mkTerm(Op op)``
            - ``Term mkTerm(Kind kind, *args)``
            - ``Term mkTerm(Op op, *args)``

            where ``*args`` is a comma-separated list of terms.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkTerm(kind_or_op, *args)

    def mkTuple(self, terms):
        """
            Create a tuple term. Terms are automatically converted if sorts are
            compatible.

            :param terms: The elements in the tuple.
            :return: The tuple Term.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkTuple(terms)

    def mkNullableSome(self, Term term):
        """
            Create a nullable some term.

            :param term: The elements value.
            :return: The element value wrapped in some constructor.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableSome(term)

    def mkNullableVal(self, Term term):
        """
            Create a selector for nullable term.

            :param term: A nullable term.
            :return: The element value of the nullable term.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableVal(term)

    def mkNullableIsNull(self, Term term):
        """
            Create a null tester for a nullable term.

            :param term: A nullable term.
            :return: A tester whether term is null.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableIsNull(term)

    def mkNullableIsSome(self, Term term):
        """
            Create a some tester for a nullable term.

            :param term: A nullable term.
            :return: A tester whether term is some.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableIsSome(term)

    def mkNullableNull(self, Sort sort):
        """
            Create a constant representing an null of the given sort.

            :param term: The sort of the Nullable element.
            :return: The null constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableNull(sort)

    def mkNullableLift(self, kind, *args):
        """
            Create a term that lifts kind to nullable terms.
            Example:
            If we have the term ((_ nullable.lift +) x y),
            where x, y of type (Nullable Int), then
            kind would be ADD, and args would be [x, y].
            This function would return
            (nullable.lift (lambda ((a Int) (b Int)) (+ a b)) x y)

            :param kind: The lifted operator.
            :param args: The arguments of the lifted operator.
            :return: A term of Kind NULLABLE_LIFT where the first child
                     is a lambda expression, and the remaining children are
                     the original arguments.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkNullableLift(kind, *args)

    def mkOp(self, k, *args):
        """
            Create operator.

            Supports the following arguments:

            - ``Op mkOp(Kind kind)``
            - ``Op mkOp(Kind kind, const string& arg)``
            - ``Op mkOp(Kind kind, uint32_t arg0, ...)``

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkOp(k, *args)

    def mkTrue(self):
        """
            Create a Boolean true constant.

            :return: The true constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkTrue()

    def mkFalse(self):
        """
            Create a Boolean false constant.

            :return: The false constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFalse()

    def mkBoolean(self, bint val):
        """
            Create a Boolean constant.

            :param val: The value of the constant.
            :return: The Boolean constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkBoolean(val)

    def mkPi(self):
        """
            Create a constant representing the number Pi.

            :return: A constant representing :py:obj:`PI <Kind.PI>`.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkPi()

    def mkInteger(self, val):
        """
            Create an integer constant.

            :param val: Representation of the constant: either a string or
                        integer.
            :return: A constant of sort Integer.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkInteger(val)

    def mkReal(self, numerator, denominator=None):
        """
            Create a real constant from a numerator and an optional denominator.

            First converts the arguments to a temporary string, either
            ``"<numerator>"`` or ``"<numerator>/<denominator>"``. This temporary
            string is forwarded to :cpp:func:`cvc5::TermManager::mkReal()` and should
            thus represent an integer, a decimal number or a fraction.

            :param numerator: The numerator.
            :param denominator: The denominator, or ``None``.
            :return: A real term with literal value.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkReal(numerator, denominator)

    def mkRegexpAll(self):
        """
            Create a regular expression all (``re.all``) term.

            :return: The all term.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkRegexpAll()

    def mkRegexpAllchar(self):
        """
            Create a regular expression allchar (``re.allchar``) term.

            :return: The allchar term.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkRegexpAllchar()

    def mkRegexpNone(self):
        """
            Create a regular expression none (``re.none``) term.

            :return: The none term.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkRegexpNone()

    def mkEmptySet(self, Sort s):
        """
            Create a constant representing an empty set of the given sort.

            :param sort: The sort of the set elements.
            :return: The empty set constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkEmptySet(s)

    def mkEmptyBag(self, Sort s):
        """
            Create a constant representing an empty bag of the given sort.

            :param sort: The sort of the bag elements.
            :return: The empty bag constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkEmptyBag(s)

    def mkSepEmp(self):
        """
            Create a separation logic empty term.

            :return: The separation logic empty term.

            .. warning::

                This function is experimental and may change in future versions.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkSepEmp()

    def mkSepNil(self, Sort sort):
        """
            Create a separation logic nil term.

            :param sort: The sort of the nil term.
            :return: The separation logic nil term.

            .. warning::

                This function is experimental and may change in future versions.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkSepNil(sort)

    def mkString(self, str s, useEscSequences = None):
        """
            Create a String constant from a ``str`` which may contain SMT-LIB
            compatible escape sequences like ``\\u1234`` to encode unicode
            characters.

            :param s: The string this constant represents.
            :param useEscSequences: Determines whether escape sequences in `s`
                                    should be converted to the corresponding
                                    unicode character
            :return: The String constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkString(s, useEscSequences)

    def mkEmptySequence(self, Sort sort):
        """
            Create an empty sequence of the given element sort.

            :param sort: The element sort of the sequence.
            :return: The empty sequence with given element sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkEmptySequence(sort)

    def mkUniverseSet(self, Sort sort):
        """
            Create a universe set of the given sort.

            :param sort: The sort of the set elements
            :return: The universe set constant

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkUniverseSet(sort)

    def mkBitVector(self, int size, *args):
        """
            Create bit-vector value.

            Supports the following arguments:

            - ``Term mkBitVector(int size, int val=0)``
            - ``Term mkBitVector(int size, string val, int base)``

            :param size: The bit-width.
            :param val: An integer representating the value, in the first form.
                        In the second form, a string representing the value.
            :param base: The base of the string representation (second form
                         only).
            :return: A Term representing a bit-vector value.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkBitVector(size, *args)

    def mkFiniteFieldElem(self, value, Sort sort, int base=10):
        """
            Create finite field value.

            Supports the following arguments:

            - ``Term mkFiniteFieldElem(int value, Sort sort)``
            - ``Term mkFiniteFieldElem(string value, Sort sort)``
            - ``Term mkFiniteFieldElem(string value, Sort sort, int base)``

            :param value: The value of the element's integer representation.
                          An integer or string of base 10 if the base is not
                          explicitly given, and else a string in the given base.
            :param sort: The field to create the element in.
            :param base: The base of the string representation of ``value``.
            :return: A Term representing a finite field value.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFiniteFieldElem(value, sort, base)

    def mkConstArray(self, Sort sort, Term val):
        """
            Create a constant array with the provided constant value stored at
            every index

            :param sort: The sort of the constant array (must be an array sort).
            :param val: The constant value to store (must match the sort's
                        element sort).
            :return: The constant array term.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkConstArray(sort, val)

    def mkFloatingPointPosInf(self, int exp, int sig):
        """
            Create a positive infinity floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPointPosInf(exp, sig)

    def mkFloatingPointNegInf(self, int exp, int sig):
        """
            Create a negative infinity floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPointNegInf(exp, sig)

    def mkFloatingPointNaN(self, int exp, int sig):
        """
            Create a not-a-number (NaN) floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPointNaN(exp, sig)

    def mkFloatingPointPosZero(self, int exp, int sig):
        """
            Create a positive zero (+0.0) floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPointPosZero(exp, sig)

    def mkFloatingPointNegZero(self, int exp, int sig):
        """
            Create a negative zero (+0.0) floating-point constant.

            :param exp: Number of bits in the exponent.
            :param sig: Number of bits in the significand.
            :return: The floating-point constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPointNegZero(exp, sig)

    def mkRoundingMode(self, rm):
        """
            Create a roundingmode constant.

            :param rm: The floating point rounding mode this constant
                       represents.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkRoundingMode(rm)

    def mkFloatingPoint(self, arg0, arg1, Term arg2):
        """
            Create a floating-point value from a bit-vector given in IEEE-754
            format, or from its three IEEE-754 bit-vector value components
            (sign bit, exponent, significand). Arguments must be either given
            as (int, int, Term) or (Term, Term, Term).

            :param arg0: The size of the exponent or the sign bit.
            :param arg1: The size of the signifcand or the bit-vector
                         representing the exponent.
            :param arg2: The value of the floating-point constant as a
                         bit-vector term or the bit-vector representing the
                         significand.
            :return: The floating-point value.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkFloatingPoint(arg0, arg1, arg2)

    def mkCardinalityConstraint(self, Sort sort, int index):
        """
            Create cardinality constraint.

            .. warning::

                This function is experimental and may change in future versions.

            :param sort: Sort of the constraint.
            :param index: The upper bound for the cardinality of the sort.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkCardinalityConstraint(sort, index)

    def mkConst(self, Sort sort, symbol=None):
        """
            Create (first-order) constant (0-arity function symbol).

            SMT-LIB:

            .. code-block:: smtlib

                ( declare-const <symbol> <sort> )
                ( declare-fun <symbol> ( ) <sort> )

            :param sort: The sort of the constant.
            :param symbol: The name of the constant. If None, a default symbol
                           is used.
            :return: The first-order constant.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkConst(sort, symbol)

    def mkVar(self, Sort sort, symbol=None):
        """
            Create a bound variable to be used in a binder (i.e. a quantifier,
            a lambda, or a witness binder).

            :param sort: The sort of the variable.
            :param symbol: The name of the variable.
            :return: The variable.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkVar(sort, symbol)

    def mkDatatypeConstructorDecl(self, str name):
        """
            Create datatype constructor declaration.

            :param name: The name of the constructor.
            :return: The datatype constructor declaration.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkDatatypeConstructorDecl(name)

    def mkDatatypeDecl(self, str name, sorts_or_bool=None, isCoDatatype=None):
        """
            Create a datatype declaration.

            :param name: The name of the datatype.
            :param isCoDatatype: True if a codatatype is to be constructed.
            :return: The datatype declaration.

            .. warning::

                This function is deprecated and will be removed in a future
                release.
        """
        return self.tm.mkDatatypeDecl(name, sorts_or_bool, isCoDatatype)

    def simplify(self, Term t, applySubs=False):
        """
            Simplify a term or formula based on rewriting and (optionally)
            applying substitutions for solved variables.

            If applySubs is true, then for example, if `(= x 0)` was asserted to
            this solver, this method may replace occurrences of `x` with `0`.

            .. warning::

                This function is experimental and may change in future versions.

            :param t: The term to simplify.
            :param applySubs: Whether to apply substitutions for solved
                              variables.
            :return: The simplified term.
        """
        return _term(self.tm, self.csolver.simplify(t.cterm, <bint> applySubs))

    def assertFormula(self, Term term):
        """
            Assert a formula

            SMT-LIB:

            .. code-block:: smtlib

                ( assert <term> )

            :param term: The formula to assert.
        """
        self.csolver.assertFormula(term.cterm)

    def checkSat(self):
        """
            Check satisfiability.

            SMT-LIB:

            .. code-block:: smtlib

                ( check-sat )

            :return: The result of the satisfiability check.
        """
        cdef Result r = Result()
        r.cr = self.csolver.checkSat()
        return r

    def mkGrammar(self, boundVars, ntSymbols):
        """
            Create a SyGuS grammar. The first non-terminal is treated as the
            starting non-terminal, so the order of non-terminals matters.

            :param boundVars: The parameters to corresponding
                              synth-fun/synth-inv.
            :param ntSymbols: The pre-declaration of the non-terminal symbols.
            :return: The grammar.
        """
        cdef vector[c_Term] bvc
        cdef vector[c_Term] ntc
        for bv in boundVars:
            bvc.push_back((<Term?> bv).cterm)
        for nt in ntSymbols:
            ntc.push_back((<Term?> nt).cterm)
        return _grammar(
            self.tm,
            self.csolver.mkGrammar(
              <const vector[c_Term]&> bvc, <const vector[c_Term]&> ntc))

    def declareSygusVar(self, str symbol, Sort sort):
        """
            Append symbol to the current list of universal variables.

            SyGuS v2:

            .. code-block:: smtlib

                ( declare-var <symbol> <sort> )

            :param sort: The sort of the universal variable.
            :param symbol: The name of the universal variable.
            :return: The universal variable.
        """
        return _term(
            self.tm,
            self.csolver.declareSygusVar(symbol.encode(), sort.csort))

    def addSygusConstraint(self, Term t):
        """
            Add a formula to the set of SyGuS constraints.

            SyGuS v2:

            .. code-block:: smtlib

                ( constraint <term> )

            :param term: The formula to add as a constraint.
        """
        self.csolver.addSygusConstraint(t.cterm)

    def getSygusConstraints(self):
        """
            Get the list of sygus constraints.
            :return: The list of sygus constraints.
        """
        constraints = []
        for c in self.csolver.getSygusConstraints():
            constraints.append(_term(self.tm, c))
        return constraints

    def addSygusAssume(self, Term t):
        """
            Add a formula to the set of Sygus assumptions.

            SyGuS v2:

            .. code-block:: smtlib

                ( assume <term> )

            :param term: The formuula to add as an assumption.
        """
        self.csolver.addSygusAssume(t.cterm)

    def getSygusAssumptions(self):
        """
            Get the list of sygus assumptions.
            :return: The list of sygus assumptions.
        """
        assumptions = []
        for a in self.csolver.getSygusAssumptions():
            assumptions.append(_term(self.tm, a))
        return assumptions

    def addSygusInvConstraint(self, Term inv_f, Term pre_f, Term trans_f, Term post_f):
        """
            Add a set of SyGuS constraints to the current state that correspond
            to an invariant synthesis problem.

            SyGuS v2:

            .. code-block:: smtlib

                ( inv-constraint <inv> <pre> <trans> <post> )

            :param inv: The function-to-synthesize.
            :param pre: The pre-condition.
            :param trans: The transition relation.
            :param post: The post-condition.
        """
        self.csolver.addSygusInvConstraint(
                inv_f.cterm, pre_f.cterm, trans_f.cterm, post_f.cterm)

    def synthFun(self, str symbol, bound_vars, Sort sort, Grammar grammar=None):
        """
            Synthesize n-ary function following specified syntactic constraints.

            SyGuS v2:

            .. code-block:: smtlib

                ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )

            :param symbol: The name of the function.
            :param boundVars: The parameters to this function.
            :param sort: The sort of the return value of this function.
            :param grammar: The syntactic constraints.
            :return: The function.
        """
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)
        if grammar is None:
          return _term(
              self.tm,
              self.csolver.synthFun(
                symbol.encode(), <const vector[c_Term]&> v, sort.csort))
        return _term(
            self.tm,
            self.csolver.synthFun(
              symbol.encode(),
              <const vector[c_Term]&> v,
              sort.csort,
              grammar.cgrammar))

    def checkSynth(self):
        """
            Try to find a solution for the synthesis conjecture corresponding
            to the current list of functions-to-synthesize, universal variables
            and constraints.

            SyGuS v2:

            .. code-block:: smtlib

                ( check-synth )

            :return: The result of the check, which is "solution" if the check
                     found a solution in which case solutions are available via
                     getSynthSolutions, "no solution" if it was determined
                     there is no solution, or "unknown" otherwise.
        """
        cdef SynthResult r = SynthResult()
        r.cr = self.csolver.checkSynth()
        return r

    def checkSynthNext(self):
        """
            Try to find a next solution for the synthesis conjecture
            corresponding to the current list of functions-to-synthesize,
            universal variables and constraints. Must be called immediately
            after a successful call to check-synth or check-synth-next.
            Requires incremental mode.

            SyGuS v2:

            .. code-block:: smtlib

                ( check-synth )

            :return: The result of the check, which is "solution" if the check
                     found a solution in which case solutions are available via
                     getSynthSolutions, "no solution" if it was determined
                     there is no solution, or "unknown" otherwise.
        """
        cdef SynthResult r = SynthResult()
        r.cr = self.csolver.checkSynthNext()
        return r

    def getSynthSolution(self, Term term):
        """
            Get the synthesis solution of the given term. This function should be
            called immediately after the solver answers unsat for sygus input.

            :param term: The term for which the synthesis solution is queried.
            :return: The synthesis solution of the given term.
        """
        return _term(self.tm, self.csolver.getSynthSolution(term.cterm))

    def getSynthSolutions(self, list terms):
        """
            Get the synthesis solutions of the given terms. This function should
            be called immediately after the solver answers unsat for sygus
            input.

            :param terms: The terms for which the synthesis solutions is
                          queried.
            :return: The synthesis solutions of the given terms.
        """
        result = []
        cdef vector[c_Term] vec
        for t in terms:
            vec.push_back((<Term?> t).cterm)
        cresult = self.csolver.getSynthSolutions(vec)
        for s in cresult:
            result.append(_term(self.tm, s))
        return result

    def findSynth(self, fst, Grammar grammar=None):
        """
            Find a target term of interest using sygus enumeration with a
            provided grammar.

            SyGuS v2:

            .. code-block:: smtlib

                ( find-synth :target G)

            :param fst: The identifier specifying what kind of term to find.
            :param grammar: The grammar for the term.
            :return: The result of the find, which is the null term if this
                     call failed.
        """
        if grammar is None:
            return _term(
                self.tm, self.csolver.findSynth(<c_FindSynthTarget> fst.value))
        return _term(
            self.tm,
            self.csolver.findSynth(
              <c_FindSynthTarget> fst.value, grammar.cgrammar))

    def findSynthNext(self):
        """
            Try to find a next solution for the synthesis conjecture
            corresponding to the current list of functions-to-synthesize,
            universal variables and constraints. Must be called immediately
            after a successful call to check-synth or check-synth-next.
            Requires incremental mode.

            SyGuS v2:

            .. code-block:: smtlib

                ( find-synth-next )

            :return: The result of the find, which is the null term if this
                     call failed.
        """
        return _term(self.tm, self.csolver.findSynthNext())

    def checkSatAssuming(self, *assumptions):
        """
            Check satisfiability assuming the given formula.

            SMT-LIB:

            .. code-block:: smtlib

                ( check-sat-assuming ( <prop_literal> ) )

            :param assumptions: The formulas to assume.
            :return: The result of the satisfiability check.
        """
        cdef Result r = Result()
        # used if assumptions is a list of terms
        cdef vector[c_Term] v
        for a in assumptions:
            v.push_back((<Term?> a).cterm)
        r.cr = self.csolver.checkSatAssuming(<const vector[c_Term]&> v)
        return r

    def declareDatatype(self, str symbol, *ctors):
        """
            Create datatype sort.

            SMT-LIB:

            .. code-block:: smtlib

                ( declare-datatype <symbol> <datatype_decl> )

            :param symbol: The name of the datatype sort.
            :param ctors: The constructor declarations of the datatype sort.
            :return: The datatype sort.
        """
        cdef vector[c_DatatypeConstructorDecl] v
        for c in ctors:
            v.push_back((<DatatypeConstructorDecl?> c).cdtconsdecl)
        return _sort(
            self.tm,
            self.csolver.declareDatatype(symbol.encode(), v))

    def declareFun(self, str symbol, list sorts, Sort sort, fresh=True):
        """
            Declare n-ary function symbol.

            SMT-LIB:

            .. code-block:: smtlib

                ( declare-fun <symbol> ( <sort>* ) <sort> )

            :param symbol: The name of the function.
            :param sorts: The sorts of the parameters to this function.
            :param sort: The sort of the return value of this function.
            :param fresh: If true, then this method always returns a new Term.
                          Otherwise, this method will always return the
                          same Term for each call with the given sorts and
                          symbol where fresh is false.
            :return: The function.
        """
        cdef vector[c_Sort] v
        for s in sorts:
            v.push_back((<Sort?> s).csort)
        return _term(self.tm, self.csolver.declareFun(symbol.encode(),
                                            <const vector[c_Sort]&> v,
                                            sort.csort,
                                            <bint> fresh))

    def declareSort(self, str symbol, int arity, fresh=True):
        """
            Declare uninterpreted sort.

            SMT-LIB:

            .. code-block:: smtlib

                ( declare-sort <symbol> <numeral> )

            .. note::

                This corresponds to :py:meth:`TermManager.mkUninterpretedSort()` if
                arity = 0, and to
                :py:meth:`TermManager.mkUninterpretedSortConstructorSort()` if
                arity > 0.

            :param symbol: The name of the sort.
            :param arity: The arity of the sort.
            :param fresh: If true, then this method always returns a new Sort.
                          Otherwise, this method will always return the same
                          Sort for each call with the given arity and symbol
                          where fresh is false.
            :return: The sort.
        """
        return _sort(
            self.tm,
            self.csolver.declareSort(symbol.encode(), arity, <bint> fresh))

    def defineFun(self, str symbol, list bound_vars, Sort sort, Term term, glbl=False):
        """
            Define n-ary function.

            SMT-LIB:

            .. code-block:: smtlib

                ( define-fun <function_def> )

            :param symbol: The name of the function.
            :param bound_vars: The parameters to this function.
            :param sort: The sort of the return value of this function.
            :param term: The function body.
            :param glbl: Determines whether this definition is global (i.e.
                         persists when popping the context).
            :return: The function.
        """
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)

        return _term(
            self.tm,
            self.csolver.defineFun(symbol.encode(),
                                           <const vector[c_Term] &> v,
                                           sort.csort,
                                           term.cterm,
                                           <bint> glbl))

    def defineFunRec(self, sym_or_fun, bound_vars, sort_or_term, t=None, glbl=False):
        """
            Define recursive functions.

            Supports the following arguments:

            - ``Term defineFunRec(str symbol, List[Term] bound_vars, Sort sort, Term term, bool glbl)``
            - ``Term defineFunRec(Term fun, List[Term] bound_vars, Term term, bool glbl)``

            SMT-LIB:

            .. code-block:: smtlib

                ( define-funs-rec ( <function_decl>^n ) ( <term>^n ) )

            Create elements of parameter ``funs`` with :py:meth:`mkConst()`.

            :param funs: The sorted functions.
            :param bound_vars: The list of parameters to the functions.
            :param terms: The list of function bodies of the functions.
            :param global: Determines whether this definition is global (i.e.
                           persists when popping the context).
            :return: The function.
        """
        cdef vector[c_Term] v
        for bv in bound_vars:
            v.push_back((<Term?> bv).cterm)

        if isinstance(sym_or_fun, str):
            return _term(
                self.tm,
                self.csolver.defineFunRec((<str?> sym_or_fun).encode(),
                                                <const vector[c_Term] &> v,
                                                (<Sort?> sort_or_term).csort,
                                                (<Term?> t).cterm,
                                                <bint> glbl))
        return _term(
            self.tm,
            self.csolver.defineFunRec((<Term?> sym_or_fun).cterm,
                                                   <const vector[c_Term]&> v,
                                                   (<Term?> sort_or_term).cterm,
                                                   <bint> glbl))

    def defineFunsRec(self, funs, bound_vars, terms, glb = False):
        """
            Define recursive functions.

            SMT-LIB:

            .. code-block:: smtlib

                ( define-funs-rec ( <function_decl>^n ) ( <term>^n ) )

            Create elements of parameter ``funs`` with :py:meth:`mkConst()`.

            :param funs: The sorted functions.
            :param bound_vars: The list of parameters to the functions.
            :param terms: The list of function bodies of the functions.
            :param glb: Determines whether this definition is global (i.e.
                        persists when popping the context).
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
            vt.push_back((<Term?> t).cterm)

        self.csolver.defineFunsRec(vf, vbv, vt, glb)

    def getProof(self, c = ProofComponent.FULL):
        """
            Get a proof associated with the most recent call to checkSat.

            SMT-LIB:

            .. code-block:: smtlib

               (get-proof :c)

            Requires to enable option
            :ref:`produce-proofs <lbl-option-produce-proofs>`.

            .. warning::

                This function is experimental and may change in future versions.

            :param c: The component of the proof to return.
            :return: A vector of proof nodes.
        """
        proofs = []
        for p in self.csolver.getProof(<c_ProofComponent> c.value):
            proofs.append(_proof(self.tm, p))
        return proofs

    def proofToString(self, proof,
                      format = ProofFormat.DEFAULT,
                      assertionNames = {}):
        """
            Prints proof into a string with a selected proof format mode.
            Other aspects of printing are taken from the solver options.

            .. warning::

                This function is experimental and may change in future versions.

            :param proof: A proof, usually obtained from
                          :py:meth:`getProof()`.
            :param format: The proof format used to print the proof.  Must be
                          "None" if the proof is not a full proof.
            :param assertionNames: Mapping between assertions and names, if
                                   they were  given by the user.  This is used
                                   by the Alethe proof format.

            :return: The proof printed in the current format.
        """
        cdef map[c_Term, string] assertionMap
        for k in assertionNames:
            assertionMap[(<Term> k).cterm] = assertionNames[k].encode('utf-8')
        return self.csolver.proofToString((<Proof?> proof).cproof,
                                         <c_ProofFormat> format.value,
                                         assertionMap)

    def getLearnedLiterals(self, type = LearnedLitType.INPUT):
        """
            Get a list of literals that are entailed by the current set of assertions

            SMT-LIB:

            .. code-block:: smtlib

                ( get-learned-literals )

            .. warning::

                This function is experimental and may change in future versions.

            :param type: The type of learned literals to return
            :return: The list of literals.
        """
        lits = []
        for a in self.csolver.getLearnedLiterals(<c_LearnedLitType> type.value):
            lits.append(_term(self.tm, a))
        return lits

    def getAssertions(self):
        """
            Get the list of asserted formulas.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-assertions )

            :return: The list of asserted formulas.
        """
        assertions = []
        for a in self.csolver.getAssertions():
            assertions.append(_term(self.tm, a))
        return assertions

    def getInfo(self, str flag):
        """
            Get info from the solver.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-info <info_flag> )

            :param flag: The info flag.
            :return: The info.
        """
        return self.csolver.getInfo(flag.encode())

    def getOption(self, str option):
        """
            Get the value of a given option.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-option <keyword> )

            :param option: The option for which the value is queried.
            :return: A string representation of the option value.
        """
        return self.csolver.getOption(option.encode()).decode()

    def getOptionNames(self):
        """
            Get all option names that can be used with
            :py:meth:`Solver.setOption()`, :py:meth:`Solver.getOption()`
            and :py:meth:`Solver.getOptionInfo()`.

        :return: All option names.
        """
        return [s.decode() for s in self.csolver.getOptionNames()]

    def getOptionInfo(self, str option):
        """
            Get some information about the given option.
            Returns the information provided by the C++
            :cpp:class:`OptionInfo <cvc5::OptionInfo>` as a dictionary.

            :return: Information about the given option.
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
            'category': OptionCategory(<int> oi.category),
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
            res['minimum'] = nii.minimum.value() \
                if nii.minimum.has_value() else None
            res['maximum'] = nii.maximum.value() \
                if nii.maximum.has_value() else None
        elif c_holds[c_OptionInfo.NumberInfo[uint64_t]](oi.valueInfo):
            # it's a uint64_t
            res['type'] = int
            niu = c_getVariant[c_OptionInfo.NumberInfo[uint64_t]](oi.valueInfo)
            res['current'] = niu.currentValue
            res['default'] = niu.defaultValue
            res['minimum'] = niu.minimum.value() \
                if niu.minimum.has_value() else None
            res['maximum'] = niu.maximum.value() \
                if niu.maximum.has_value() else None
        elif c_holds[c_OptionInfo.NumberInfo[double]](oi.valueInfo):
            # it's a double
            res['type'] = float
            nid = c_getVariant[c_OptionInfo.NumberInfo[double]](oi.valueInfo)
            res['current'] = nid.currentValue
            res['default'] = nid.defaultValue
            res['minimum'] = nid.minimum.value() \
                if nid.minimum.has_value() else None
            res['maximum'] = nid.maximum.value() \
                if nid.maximum.has_value() else None
        elif c_holds[c_OptionInfo.ModeInfo](oi.valueInfo):
            # it's a mode
            res['type'] = 'mode'
            mi = c_getVariant[c_OptionInfo.ModeInfo](oi.valueInfo)
            res['current'] = mi.currentValue.decode()
            res['default'] = mi.defaultValue.decode()
            res['modes'] = [s.decode() for s in mi.modes]
        return res

    def getUnsatAssumptions(self):
        """
            Get the set of unsat ("failed") assumptions.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-unsat-assumptions )

            Requires to enable option :ref:`produce-unsat-assumptions
            <lbl-option-produce-unsat-assumptions>`.

            :return: The set of unsat assumptions.
        """
        assumptions = []
        for a in self.csolver.getUnsatAssumptions():
            assumptions.append(_term(self.tm, a))
        return assumptions

    def getUnsatCore(self):
        """
            Get the unsatisfiable core.

            SMT-LIB:

            .. code-block:: smtlib

              (get-unsat-core)

            Requires to enable option :ref:`produce-unsat-cores
            <lbl-option-produce-unsat-cores>`.

            .. note::

                In contrast to SMT-LIB, the API does not distinguish between
                named and unnamed assertions when producing an unsatisfiable
                core. Additionally, the API allows this option to be called
                after a check with assumptions. A subset of those assumptions
                may be included in the unsatisfiable core returned by this
                method.

            :return: A set of terms representing the unsatisfiable core.
        """
        core = []
        for a in self.csolver.getUnsatCore():
            core.append(_term(self.tm, a))
        return core

    def getUnsatCoreLemmas(self):
        """
            Get the lemmas used to derive unsatisfiability.

            SMT-LIB:

            .. code-block:: smtlib

                (get-unsat-core-lemmas)

            Requires the SAT proof unsat core mode, so to enable option
            :ref:`unsat-cores-mode=sat-proof <lbl-option-unsat-cores-mode>`.

            .. warning::

                This function is experimental and may change in future versions.

            :return: A set of terms representing the lemmas used to derive
                     unsatisfiability.
        """
        coreLemmas = []
        for a in self.csolver.getUnsatCoreLemmas():
            coreLemmas.append(_term(self.tm, a))
        return coreLemmas

    def getDifficulty(self):
        """
            Get a difficulty estimate for an asserted formula. This function is
            intended to be called immediately after any response to a
            :py:meth:`Solver.checkSat()` call.

            .. warning::

                This function is experimental and may change in future versions.

            :return: A map from (a subset of) the input assertions to a real
                     value that is an estimate of how difficult each assertion
                     was to solver. Unmentioned assertions can be assumed to
                     have zero difficulty.
        """
        diffi = {}
        for p in self.csolver.getDifficulty():
            k = p.first
            v = p.second
            termk = _term(self.tm, k)
            termv = _term(self, v)
            diffi[termk] = termv
        return diffi

    def getTimeoutCore(self):
        """
            Get a timeout core, which computes a subset of the current
            assertions that cause a timeout. Note it does not require being
            proceeded by a call to checkSat.

            This function may make multiple checks for satisfiability internally,
            each limited by the timeout value given by
            :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.

            .. code-block:: smtlib

                (get-timeout-core)

            .. warning::

                This function is experimental and may change in future versions.

            :return: The result of the timeout core computation. This is a pair
                     containing a result and a list of formulas. If the result is unknown
                     and the reason is timeout, then the list of formulas correspond to a
                     subset of the current assertions that cause a timeout in the
                     specified time
                     :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.
                     If the result is unsat, then the list of formulas correspond to an
                     unsat core for the current assertions. Otherwise, the result is sat,
                     indicating that the current assertions are satisfiable, and
                     the list of formulas is empty.
        """
        cdef pair[c_Result, vector[c_Term]] res
        res = self.csolver.getTimeoutCore()
        core = []
        for a in res.second:
            core.append(_term(self.tm, a))
        cdef Result r = Result()
        r.cr = res.first
        return (r, core)

    def getTimeoutCoreAssuming(self, *assumptions):
        """
            Get a timeout core, which computes a subset of the given assumptions
            that cause a timeout when added to the current assertions. Note it
            does not require being proceeded by a call to checkSat.

            This function may make multiple checks for satisfiability internally,
            each limited by the timeout value given by
            :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.

            .. code-block:: smtlib

                (get-timeout-core)

            .. warning::

                This function is experimental and may change in future versions.

            :param assumptions: The formulas to assume.
            :return: The result of the timeout core computation. This is a pair
                     containing a result and a list of formulas. If the result is unknown
                     and the reason is timeout, then the list of formulas correspond to a
                     subset of assumptions that cause a timeout when added to the current
                     assertions in the specified time
                     :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.
                     If the result is unsat, then the list of formulas plus the current
                     assertions correspond to an unsat core for the current assertions.
                     Otherwise, the result is sat, indicating that the given assumptions plus
                     the current assertions are satisfiable, and the list of formulas is empty.
        """
        cdef vector[c_Term] v
        for a in assumptions:
            v.push_back((<Term?> a).cterm)
        cdef pair[c_Result, vector[c_Term]] res
        res = self.csolver.getTimeoutCoreAssuming(v)
        core = []
        for ac in res.second:
            core.append(_term(self.tm, ac))
        cdef Result r = Result()
        r.cr = res.first
        return (r, core)

    def getValue(self, term_or_list):
        """
            Get the value of the given term or list of terms in the current
            model.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-value ( <term>* ) )

            :param term_or_list: The term or list of terms for which the value
                                 is queried.
            :return: The value or list of values of the given term or list of
                     terms.
        """
        if isinstance(term_or_list, list):
            return [self.getValue(t) for t in term_or_list]
        return _term(self.tm, self.csolver.getValue((<Term> term_or_list).cterm))

    def getModelDomainElements(self, Sort s):
        """
            Get the domain elements of uninterpreted sort s in the current
            model. The current model interprets s as the finite sort whose
            domain elements are given in the return value of this method.

            :param s: The uninterpreted sort in question.
            :return: The domain elements of s in the current model.
        """
        result = []
        cresult = self.csolver.getModelDomainElements(s.csort)
        for e in cresult:
            result.append(_term(self.tm, e))
        return result

    def isModelCoreSymbol(self, Term v):
        """
            This returns False if the model value of free constant v was not
            essential for showing the satisfiability of the last call to
            checkSat using the current model. This function will only return
            false (for any v) if the model-cores option has been set.

            .. warning::

                This function is experimental and may change in future versions.

            :param v: The term in question.
            :return: True if v is a model core symbol.
        """
        return self.csolver.isModelCoreSymbol(v.cterm)

    def getQuantifierElimination(self, Term term):
        """
            Do quantifier elimination.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-qe <q> )

            Requires a logic that supports quantifier elimination.
            Currently, the only logics supported by quantifier elimination
            are LRA and LIA.

            .. warning::

                This function is experimental and may change in future versions.

            :param q: A quantified formula of the form
                      :math:`Q\\bar{x_1}\\dots Q\\bar{x}_n. P( x_1 \\dots x_i, y_1 \\dots y_j)`
                      where
                      :math:`Q\\bar{x}` is a set of quantified variables of the
                      form :math:`Q x_1...x_k` and
                      :math:`P( x_1...x_i, y_1...y_j )` is a quantifier-free
                      formula
            :return: A formula :math:`\\phi` such that, given the current set
                     of formulas :math:`A` asserted to this solver:

                     - :math:`(A \\wedge q)` :math:`(A \\wedge \\phi)` are
                       equivalent
                     - :math:`\\phi` is quantifier-free formula containing only
                       free variables in :math:`y_1...y_n`.
        """
        return _term(self.tm, self.csolver.getQuantifierElimination(term.cterm))

    def getQuantifierEliminationDisjunct(self, Term term):
        """
            Do partial quantifier elimination, which can be used for
            incrementally computing the result of a quantifier elimination.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-qe-disjunct <q> )

            Requires a logic that supports quantifier elimination.
            Currently, the only logics supported by quantifier elimination
            are LRA and LIA.

          .. warning::

              This function is experimental and may change in future versions.

            :param q: A quantified formula of the form
                 :math:`Q\\bar{x_1} ... Q\\bar{x_n}. P( x_1...x_i, y_1...y_j)`
                 where :math:`Q\\bar{x}` is a set of quantified variables of
                 the form :math:`Q x_1...x_k` and
                 :math:`P( x_1...x_i, y_1...y_j )` is a quantifier-free formula.

            :return: A formula :math:`\\phi` such that, given the current set
                 of formulas :math:`A` asserted to this solver:

                 - :math:`(A \\wedge q \\implies A \\wedge \\phi)` if :math:`Q`
                   is :math:`\\forall`, and
                   :math:`(A \\wedge \\phi \\implies A \\wedge q)` if
                   :math:`Q` is :math:`\\exists`
                 - :math:`\\phi` is quantifier-free formula containing only
                   free variables in :math:`y_1...y_n`
                 - If :math:`Q` is :math:`\\exists`, let :math:`(A \\wedge Q_n)`
                   be the formula
                   :math:`(A \\wedge \\neg (\\phi \\wedge Q_1) \\wedge ... \\wedge \\neg (\\phi \\wedge Q_n))`
                   where for each :math:`i = 1...n`, formula
                   :math:`(\\phi \\wedge Q_i)` is the result of calling
                   :py:meth:`getQuantifierEliminationDisjunct()`
                   for :math:`q` with the set of assertions
                   :math:`(A \\wedge Q_{i-1})`.
                   Similarly, if :math:`Q` is :math:`\\forall`, then let
                   :math:`(A \\wedge Q_n)` be
                   :math:`(A \\wedge (\\phi \\wedge Q_1) \\wedge ... \\wedge (\\phi \\wedge Q_n))`
                   where :math:`(\\phi \\wedge Q_i)` is the same as above.
                   In either case, we have that :math:`(\\phi \\wedge Q_j)`
                   will eventually be true or false, for some finite :math:`j`.
        """
        return _term(
            self.tm,
            self.csolver.getQuantifierEliminationDisjunct(term.cterm))

    def getModel(self, sorts, consts):
        """
            Get the model

            SMT-LIB:

            .. code:: smtlib

                (get-model)

            Requires to enable option
            :ref:`produce-models <lbl-option-produce-models>`.

            .. warning::

                This function is experimental and may change in future versions.

            :param sorts: The list of uninterpreted sorts that should be
                          printed in the model.
            :param vars: The list of free constants that should be printed in
                         the model. A subset of these may be printed based on
                         :py:meth:`Solver.isModelCoreSymbol()`.
            :return: A string representing the model.
        """

        cdef vector[c_Sort] csorts
        for sort in sorts:
            csorts.push_back((<Sort?> sort).csort)

        cdef vector[c_Term] cconsts
        for const in consts:
            cconsts.push_back((<Term?> const).cterm)

        return self.csolver.getModel(csorts, cconsts)

    def getValueSepHeap(self):
        """
            When using separation logic, obtain the term for the heap.

            .. warning::

                This function is experimental and may change in future versions.

            :return: The term for the heap.
        """
        return _term(self.tm, self.csolver.getValueSepHeap())

    def getValueSepNil(self):
        """
            When using separation logic, obtain the term for nil.

            .. warning::

                This function is experimental and may change in future versions.

            :return: The term for nil.
        """
        return _term(self.tm, self.csolver.getValueSepNil())

    def declareSepHeap(self, Sort locType, Sort dataType):
        """
            When using separation logic, this sets the location sort and the
            datatype sort to the given ones. This function should be invoked
            exactly once, before any separation logic constraints are provided.

            .. warning::

                This function is experimental and may change in future versions.

            :param locSort: The location sort of the heap.
            :param dataSort: The data sort of the heap.
        """
        self.csolver.declareSepHeap(locType.csort, dataType.csort)

    def declarePool(self, str symbol, Sort sort, initValue):
        """
            Declare a symbolic pool of terms with the given initial value.

            SMT-LIB:

            .. code-block:: smtlib

                ( declare-pool <symbol> <sort> ( <term>* ) )

            .. warning::

                This function is experimental and may change in future versions.

            :param symbol: The name of the pool.
            :param sort: The sort of the elements of the pool.
            :param initValue: The initial value of the pool.
        """
        cdef vector[c_Term] niv
        for v in initValue:
            niv.push_back((<Term?> v).cterm)
        return _term(
            self.tm,
            self.csolver.declarePool(symbol.encode(), sort.csort, niv))

    def addPlugin(self, Plugin p):
        """
            Add plugin to this solver. Its callbacks will be called throughout the
            lifetime of this solver.

            :param p: The plugin to add to this solver.
        """
        cdef c_Plugin* ptr = <c_Plugin*> p.cplugin
        self.csolver.addPlugin(dereference(ptr))

    def pop(self, nscopes=1):
        """
            Pop ``nscopes`` level(s) from the assertion stack.

            SMT-LIB:

            .. code-block:: smtlib

                ( pop <numeral> )

            :param nscopes: The number of levels to pop.
        """
        self.csolver.pop(nscopes)

    def push(self, nscopes=1):
        """
            Push ``nscopes`` level(s) to the assertion stack.

            SMT-LIB:

            .. code-block:: smtlib

                ( push <numeral> )

            :param nscopes: The number of levels to push.
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
        """
            Set info.

            SMT-LIB:

            .. code-block:: smtlib

                ( set-info <attribute> )

            :param keyword: The info flag.
            :param value: The value of the info flag.
        """
        self.csolver.setInfo(keyword.encode(), value.encode())

    def setLogic(self, str logic):
        """
            Set logic.

            SMT-LIB:

            .. code-block:: smtlib

                ( set-logic <symbol> )

            :param logic: The logic to set.
        """
        self.csolver.setLogic(logic.encode())

    def isLogicSet(self):
        """
            Is logic set? Returns whether we called setLogic yet for this
            solver.

            :return: whether we called setLogic yet for this solver.
        """
        return self.csolver.isLogicSet()

    def getLogic(self):
        """
            Get the logic set the solver.

            .. note:: Asserts isLogicSet().

            :return: The logic used by the solver.
        """
        return self.csolver.getLogic().decode()

    def setOption(self, str option, str value):
        """
            Set option.

            SMT-LIB:

            .. code-block:: smtlib

                ( set-option <option> )

            :param option: The option name.
            :param value: The option value.
        """
        self.csolver.setOption(option.encode(), value.encode())


    def getInterpolant(self, Term conj, Grammar grammar=None):
        """
            Get an interpolant.
	    Assuming that :math:`A \\rightarrow B` is valid,
	    this function
            determines a term :math:`I`
	    over the shared variables of 
            :math:`A` and :math:`B`,
	    optionally with respect to a
            a given grammar, such that :math:`A \\rightarrow I` and
            :math:`I \\rightarrow B` are valid, if such a term exits.
            :math:`A` is the current set of assertions and :math:`B` is the
            conjecture, given as :code:`conj`.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-interpolant <symbol> <conj> )
                ( get-interpolant <symbol> <conj> <grammar> )

            .. note:: In SMT-LIB, :code:`<symbol>` assigns a symbol to the
                      interpolant.

            .. note:: Requires option
                 :ref:`produce-interpolants <lbl-option-produce-interpolants>`
                 to be set to a mode different from :code:`none`.

            .. warning::

                This function is experimental and may change in future versions.

            :param conj: The conjecture term.
            :param grammar: A grammar for the interpolant.
            :return: The interpolant, if such a term exists.
        """
        if grammar is None:
            return _term(self.tm, self.csolver.getInterpolant(conj.cterm))
        return _term(
            self.tm,
            self.csolver.getInterpolant(conj.cterm, grammar.cgrammar))


    def getInterpolantNext(self):
        """
            Get the next interpolant.

            Can only be called immediately after a successful call to
            :py:func:`Solver.getInterpolant()` or
            :py:func:`Solver.getInterpolantNext()`.
            Is guaranteed to produce a syntactically different interpolant wrt
            the last returned interpolant if successful.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-interpolant-next )

            Requires to enable incremental mode, and option
            :ref:`produce-interpolants <lbl-option-produce-interpolants>` to be
            set to a mode different from ``none``.

            .. warning::

                This function is experimental and may change in future versions.

            :param output: The term where the result will be stored.
            :return: True iff an interpolant was found.
        """
        return _term(self.tm, self.csolver.getInterpolantNext())


    def getAbduct(self, Term conj, Grammar grammar=None):
        """
            Get an abduct.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-abduct <conj> )
                ( get-abduct <conj> <grammar> )

            Requires to enable option
            :ref:`produce-abducts <lbl-option-produce-abducts>`.

            .. warning::

                This function is experimental and may change in future versions.

            :param conj: The conjecture term.
            :param grammar: A grammar for the abduct.
            :return: The abduct.
                     See :cpp:func:`cvc5::Solver::getAbduct` for details.
        """
        if grammar is None:
            return _term(self.tm, self.csolver.getAbduct(conj.cterm))
        return _term(
            self.tm,
            self.csolver.getAbduct(conj.cterm, grammar.cgrammar))

    def getAbductNext(self):
        """
            Get the next abduct.

            Can only be called immediately after a successful call to
            :py:func:`Solver.getAbduct()` or
            :py:func:`Solver.getAbductNext()`.
            Is guaranteed to produce a syntactically different abduct wrt the
            last returned abduct if successful.

            SMT-LIB:

            .. code-block:: smtlib

                ( get-abduct-next )

            Requires to enable incremental mode, and
            option :ref:`produce-abducts <lbl-option-produce-abducts>`.

            .. warning::

                This function is experimental and may change in future versions.

            :param output: The term where the result will be stored.
            :return: True iff an abduct was found.
        """
        return _term(self.tm, self.csolver.getAbductNext())

    def blockModel(self, mode):
        """
            Block the current model. Can be called only if immediately preceded
            by a SAT or INVALID query.

            SMT-LIB:

            .. code-block:: smtlib

                (block-model)

            Requires enabling option
            :ref:`produce-models <lbl-option-produce-models>`
            to a mode other than ``none``.

            .. warning::

                This function is experimental and may change in future versions.

            :param mode: The mode to use for blocking
        """
        self.csolver.blockModel(<c_BlockModelsMode> mode.value)

    def blockModelValues(self, terms):
        """
           Block the current model values of (at least) the values in terms.
           Can be called only if immediately preceded by a SAT query.

           SMT-LIB:

           .. code-block:: smtlib

              (block-model-values ( <terms>+ ))

           Requires enabling option
           :ref:`produce-models <lbl-option-produce-models>`.

           .. warning::

                This function is experimental and may change in future versions.
        """
        cdef vector[c_Term] nts
        for t in terms:
            nts.push_back((<Term?> t).cterm)
        self.csolver.blockModelValues(nts)

    def getInstantiations(self):
        """
            Return a string that contains information about all instantiations
            made by the quantifiers module.

            .. warning::

                This function is experimental and may change in future versions.
        """
        return self.csolver.getInstantiations()

    def getStatistics(self):
        """
            Return a snapshot of the current state of the statistic values of
            this solver. The returned object is completely decoupled from the
            solver and will not change when the solver is used again.
        """
        res = Statistics()
        res.cstats = self.csolver.getStatistics()
        return res

    def getVersion(self):
        """
            Return a string representation of the version of this solver.
        """
        return self.csolver.getVersion()


# ----------------------------------------------------------------------------
# Sort
# ----------------------------------------------------------------------------

cdef class Sort:
    """
        The sort of a cvc5 term.

        Wrapper class for :cpp:class:`cvc5::Sort`.
    """
    cdef c_Sort csort
    cdef TermManager tm

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

    def getKind(self):
        """
            .. warning::

                This function is experimental and may change in future versions.

            :return: The :py:class:`SortKind` of this sort.
        """
        return SortKind(<int> self.csort.getKind())

    def hasSymbol(self):
        """
            :return: True iff this sort has a symbol.
        """
        return self.csort.hasSymbol()

    def getSymbol(self):
        """
            .. note:: Asserts :py:meth:`hasSymbol()`.

            :return: The raw symbol of the sort.
        """
        return self.csort.getSymbol().decode()

    def isNull(self):
        """
            :return: True if this Sort is a null sort.
        """
        return self.csort.isNull()

    def isBoolean(self):
        """
            Determine if this is the Boolean sort (SMT-LIB: ``Bool``).

            :return: True if the sort is the Boolean sort.
        """
        return self.csort.isBoolean()

    def isInteger(self):
        """
            Determine if this is the integer sort (SMT-LIB: ``Int``).

            :return: True if the sort is the integer sort.
        """
        return self.csort.isInteger()

    def isReal(self):
        """
            Determine if this is the real sort (SMT-LIB: `Real`).

            :return: True if the sort is the real sort.
        """
        return self.csort.isReal()

    def isString(self):
        """
            Determine if this is the string sort (SMT-LIB: `String`).

            :return: True if the sort is the string sort.
        """
        return self.csort.isString()

    def isRegExp(self):
        """
            Determine if this is the regular expression sort (SMT-LIB:
            ``RegLan``).

            :return: True if the sort is the regexp sort.
        """
        return self.csort.isRegExp()

    def isRoundingMode(self):
        """
            Determine if this is the rounding mode sort (SMT-LIB:
            ``RoundingMode``).

            :return: True if the sort is the rounding mode sort.
        """
        return self.csort.isRoundingMode()

    def isBitVector(self):
        """
            Determine if this is a bit-vector sort (SMT-LIB: ``(_ BitVec i)``).

            :return: True if the sort is a bit-vector sort.
        """
        return self.csort.isBitVector()

    def isFloatingPoint(self):
        """
            Determine if this is a floatingpoint sort
            (SMT-LIB: ``(_ FloatingPoint eb sb)``).

            :return: True if the sort is a bit-vector sort.
        """
        return self.csort.isFloatingPoint()

    def isDatatype(self):
        """
            Determine if this is a datatype sort.

            :return: True if the sort is a datatype sort.
        """
        return self.csort.isDatatype()

    def isDatatypeConstructor(self):
        """
            Determine if this is a datatype constructor sort.

            :return: True if the sort is a datatype constructor sort.
        """
        return self.csort.isDatatypeConstructor()

    def isDatatypeSelector(self):
        """
            Determine if this is a datatype selector sort.

            :return: True if the sort is a datatype selector sort.
        """
        return self.csort.isDatatypeSelector()

    def isDatatypeTester(self):
        """
            Determine if this is a tester sort.

            :return: True if the sort is a selector sort.
        """
        return self.csort.isDatatypeTester()

    def isDatatypeUpdater(self):
        """
            Determine if this is a datatype updater sort.

            :return: True if the sort is a datatype updater sort.
        """
        return self.csort.isDatatypeUpdater()

    def isFunction(self):
        """
            Determine if this is a function sort.

            :return: True if the sort is a function sort.
        """
        return self.csort.isFunction()

    def isPredicate(self):
        """
            Determine if this is a predicate sort.

            A predicate sort is a function sort that maps to the Boolean sort.
            All predicate sorts are also function sorts.

            :return: True if the sort is a predicate sort.
        """
        return self.csort.isPredicate()

    def isTuple(self):
        """
            Determine if this is a tuple sort.

            :return: True if the sort is a tuple sort.
        """
        return self.csort.isTuple()

    def isNullable(self):
        """
            Determine if this is a nullable sort.

            :return: True if the sort is a nullable sort.
        """
        return self.csort.isNullable()

    def isRecord(self):
        """
            Determine if this is a record sort.

            .. warning::

                This function is experimental and may change in future versions.

            :return: True if the sort is a record sort.
        """
        return self.csort.isRecord()

    def isArray(self):
        """
            Determine if this is an array sort.

            :return: True if the sort is an array sort.
        """
        return self.csort.isArray()

    def isFiniteField(self):
        """
            Determine if this is a finite field sort.

            :return: True if the sort is an array sort.
        """
        return self.csort.isFiniteField()

    def isSet(self):
        """
            Determine if this is a set sort.

            :return: True if the sort is a set sort.
        """
        return self.csort.isSet()

    def isBag(self):
        """
            Determine if this is a bag sort.

            :return: True if the sort is a bag sort.
        """
        return self.csort.isBag()

    def isSequence(self):
        """
            Determine if this is a sequence sort.

            :return: True if the sort is a sequence sort.
        """
        return self.csort.isSequence()

    def isAbstract(self):
        """
            Determine if this is an abstract sort.

            :return: True if the sort is an abstract sort.

            .. warning::

                This function is experimental and may change in future versions.
        """
        return self.csort.isAbstract()

    def isUninterpretedSort(self):
        """
            Determine if this is a sort uninterpreted.

            :return: True if the sort is uninterpreted.
        """
        return self.csort.isUninterpretedSort()

    def isUninterpretedSortConstructor(self):
        """
            Determine if this is a sort constructor kind.

            An uninterpreted sort constructor is an uninterpreted sort with
            arity > 0.

            :return: True if this a sort constructor kind.
        """
        return self.csort.isUninterpretedSortConstructor()

    def isInstantiated(self):
        """
            Determine if this is an instantiated (parametric datatype or
            uninterpreted sort constructor) sort.

            An instantiated sort is a sort that has been constructed from
            instantiating a sort parameters with sort arguments
            (see :py:meth:`instantiate()`).

            :return: True if this is an instantiated sort.
        """
        return self.csort.isInstantiated()

    def getUninterpretedSortConstructor(self):
        """
            Get the associated uninterpreted sort constructor of an
            instantiated uninterpreted sort.

            :return: The uninterpreted sort constructor sort
        """
        return _sort(self.tm, self.csort.getUninterpretedSortConstructor())

    def getDatatype(self):
        """
            :return: The underlying datatype of a datatype sort
        """
        return _datatype(self.tm, self.csort.getDatatype())

    def instantiate(self, params):
        """
            Instantiate a parameterized datatype sort or uninterpreted sort
            constructor sort.

            Create sorts parameter with :py:meth:`TermManager.mkParamSort()`

            .. warning::

                This function is experimental and may change in future versions.

            :param params: The list of sort parameters to instantiate with
            :return: The instantiated sort
        """
        cdef vector[c_Sort] v
        for s in params:
            v.push_back((<Sort?> s).csort)
        return _sort(self.tm, self.csort.instantiate(v))

    def getInstantiatedParameters(self):
        """
            Get the sorts used to instantiate the sort parameters of a
            parametric sort (parametric datatype or uninterpreted sort
            constructor sort, see :py:meth:`instantiate()`).

            :return: The sorts used to instantiate the sort parameters of a
                     parametric sort
        """
        instantiated_sorts = []
        for s in self.csort.getInstantiatedParameters():
            instantiated_sorts.append(_sort(self.tm, s))
        return instantiated_sorts

    def substitute(self, sort_or_list_1, sort_or_list_2):
        """
            Substitution of Sorts.

            Note that this replacement is applied during a pre-order traversal
            and only once to the sort. It is not run until fix point. In the
            case that sort_or_list_1 contains duplicates, the replacement
            earliest in the list takes priority.

            For example,
            ``(Array A B) .substitute([A, C], [(Array C D), (Array A B)])``
            will return ``(Array (Array C D) B)``.

            .. warning::

                This function is experimental and may change in future versions.

            :param sort_or_list_1: The subsort or subsorts to be substituted
                                   within this sort.
            :param sort_or_list_2: The sort or list of sorts replacing the
                                   substituted subsort.
        """

        # lists for substitutions
        cdef vector[c_Sort] ces
        cdef vector[c_Sort] creplacements

        if isinstance(sort_or_list_1, list):
            # call the API substitute method with lists
            assert isinstance(sort_or_list_2, list)
            es = sort_or_list_1
            replacements = sort_or_list_2
            if len(es) != len(replacements):
                raise RuntimeError("Expecting list inputs to substitute to "
                                   "have the same length but got: "
                                   "{} and {}".format(
                                       len(es), len(replacements)))

            for e, r in zip(es, replacements):
                ces.push_back((<Sort?> e).csort)
                creplacements.push_back((<Sort?> r).csort)
            return _sort(self.tm, self.csort.substitute(ces, creplacements))
        # call the API substitute method with single sorts
        return _sort(
            self.tm,
            self.csort.substitute(
              (<Sort?> sort_or_list_1).csort, (<Sort?> sort_or_list_2).csort))


    def getDatatypeConstructorArity(self):
        """
            :return: The arity of a datatype constructor sort.
        """
        return self.csort.getDatatypeConstructorArity()

    def getDatatypeConstructorDomainSorts(self):
        """
            :return: The domain sorts of a datatype constructor sort.
        """
        domain_sorts = []
        for s in self.csort.getDatatypeConstructorDomainSorts():
            domain_sorts.append(_sort(self.tm, s))
        return domain_sorts

    def getDatatypeConstructorCodomainSort(self):
        """
            :return: The codomain sort of a datatype constructor sort.
        """
        return _sort(self.tm, self.csort.getDatatypeConstructorCodomainSort())

    def getDatatypeSelectorDomainSort(self):
        """
            :return: The domain sort of a datatype selector sort.
        """
        return _sort(self.tm, self.csort.getDatatypeSelectorDomainSort())

    def getDatatypeSelectorCodomainSort(self):
        """
            :return: The codomain sort of a datatype selector sort.
        """
        return _sort(self.tm, self.csort.getDatatypeSelectorCodomainSort())

    def getDatatypeTesterDomainSort(self):
        """
            :return: The domain sort of a datatype tester sort.
        """
        return _sort(self.tm, self.csort.getDatatypeTesterDomainSort())

    def getDatatypeTesterCodomainSort(self):
        """
            :return: the codomain sort of a datatype tester sort, which is the
                     Boolean sort
        """
        return _sort(self.tm, self.csort.getDatatypeTesterCodomainSort())

    def getFunctionArity(self):
        """
            :return: The arity of a function sort.
        """
        return self.csort.getFunctionArity()

    def getFunctionDomainSorts(self):
        """
            :return: The domain sorts of a function sort.
        """
        domain_sorts = []
        for s in self.csort.getFunctionDomainSorts():
            domain_sorts.append(_sort(self.tm, s))
        return domain_sorts

    def getFunctionCodomainSort(self):
        """
            :return: The codomain sort of a function sort.
        """
        return _sort(self.tm, self.csort.getFunctionCodomainSort())

    def getArrayIndexSort(self):
        """
            :return: The array index sort of an array sort.
        """
        return _sort(self.tm, self.csort.getArrayIndexSort())

    def getArrayElementSort(self):
        """
            :return: The array element sort of an array sort.
        """
        return _sort(self.tm, self.csort.getArrayElementSort())

    def getSetElementSort(self):
        """
            :return: The element sort of a set sort.
        """
        return _sort(self.tm, self.csort.getSetElementSort())

    def getBagElementSort(self):
        """
            :return: The element sort of a bag sort.
        """
        return _sort(self.tm, self.csort.getBagElementSort())

    def getSequenceElementSort(self):
        """
            :return: The element sort of a sequence sort.
        """
        return _sort(self.tm, self.csort.getSequenceElementSort())

    def getAbstractedKind(self):
        """
            :return: The sort kind of an abstract sort, which denotes the kind
                     of sorts that this abstract sort denotes.

            .. warning::

                This function is experimental and may change in future versions.

        """
        return SortKind(<int> self.csort.getAbstractedKind())

    def getUninterpretedSortConstructorArity(self):
        """
            :return: The arity of a sort constructor sort.
        """
        return self.csort.getUninterpretedSortConstructorArity()

    def getBitVectorSize(self):
        """
            :return: The bit-width of the bit-vector sort.
        """
        return self.csort.getBitVectorSize()

    def getFiniteFieldSize(self):
        """
            :return: The size of the finite field sort.
        """
        return int(self.csort.getFiniteFieldSize().decode())

    def getFloatingPointExponentSize(self):
        """
            :return: The bit-width of the exponent of the floating-point sort.
        """
        return self.csort.getFloatingPointExponentSize()

    def getFloatingPointSignificandSize(self):
        """
            :return: The width of the significand of the floating-point sort.
        """
        return self.csort.getFloatingPointSignificandSize()

    def getDatatypeArity(self):
        """
            :return: The arity of a datatype sort.
        """
        return self.csort.getDatatypeArity()

    def getTupleLength(self):
        """
            :return: The length of a tuple sort.
        """
        return self.csort.getTupleLength()

    def getTupleSorts(self):
        """
            :return: The element sorts of a tuple sort.
        """
        tuple_sorts = []
        for s in self.csort.getTupleSorts():
            tuple_sorts.append(_sort(self.tm, s))
        return tuple_sorts

    def getNullableElementSort(self):
        """
            :return: The element sort of a nullable sort.
        """
        return _sort(self.tm, self.csort.getNullableElementSort())


# ----------------------------------------------------------------------------
# Statistics
# ----------------------------------------------------------------------------

cdef class Statistics:
    """
        The cvc5 Statistics.

        Wrapper class for :cpp:class:`cvc5::Statistics`.

        Obtain a single statistic value using ``stats["name"]`` and a
        dictionary with, configurably all (including internal and unchanged)
        statistics using :meth:`Statistics.get()`.

        Iterate over all (including internal and unchanged) statistics via (the
        standard iterable functions) :meth:`__iter__()` and :meth:`__next__()`.
    """
    cdef c_Statistics cstats
    cdef c_Statistics.iterator cit

    def __init__(self):
        # Initialize iterator to begin() to avoid erroneous behavior due to
        # calling __next__() immediately after creation of the statistics
        # object. Note that this will not enable iteration (for this __iter__()
        # has to be called first)
        self.cit = self.cstats.begin(<bint> True, <bint> True)

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
            'default': s.isDefault(),
            'internal': s.isInternal(),
            'value': res
        }

    def __getitem__(self, str name):
        """
            Get the statistics information for the statistic called ``name``.

            :param name: The name of the statistic to get.
        """
        return self.__stat_to_dict(self.cstats.get(name.encode()))

    def __iter__(self):
        """
            Iterate over all statistics (including internal and unchanged
            statistics).
        """
        self.cit = self.cstats.begin(<bint> True, <bint> True)
        return self

    def __next__(self):
        """
            Get next statistic as a pair ``[name, <dict: name -> value>]``.
        """
        if self.cit != self.cstats.end():
            s = &dereference(self.cit)
            preincrement(self.cit)
            return [s.first.decode(), self.__stat_to_dict(s.second)]
        raise StopIteration

    def get(self, bint internal = False, bint defaulted = False):
        """
            Get all statistics as a dictionary.

            :param internal:  True to also inclue internal statistics.
            :param defaulted: True to also include unchanged statistics.
            :return: A dictionary with all available statistics.
        """
        cdef c_Statistics.iterator it = self.cstats.begin(internal, defaulted)
        cdef pair[string,c_Stat]* s
        res = {}
        while it != self.cstats.end():
            s = &dereference(it)
            res[s.first.decode()] = self.__stat_to_dict(s.second)
            preincrement(it)
        return res


# ----------------------------------------------------------------------------
# Term
# ----------------------------------------------------------------------------

cdef class Term:
    """
        A cvc5 Term.

        Wrapper class for :cpp:class:`cvc5::Term`.
    """
    cdef c_Term cterm
    cdef TermManager tm

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
        """
            Get the child term at a given index.

            :param index: The index of the child term to return.
            :return: The child term with the given index.
        """
        if index < 0:
            raise ValueError("Expecting a non-negative integer or string")
        return _term(self.tm, self.cterm[index])

    def __str__(self):
        return self.cterm.toString().decode()

    def __repr__(self):
        return self.cterm.toString().decode()

    def __iter__(self):
        """Iterate over all child terms."""
        for ci in self.cterm:
            yield _term(self.tm, ci)

    def __hash__(self):
        return ctermhash(self.cterm)

    def getNumChildren(self):
        """
            :return: The number of children of this term.
        """
        return self.cterm.getNumChildren()

    def getId(self):
        """
            :return: The id of this term.
        """
        return self.cterm.getId()

    def getKind(self):
        """
            :return: The :py:class:`Kind` of this term.
        """
        return Kind(<int> self.cterm.getKind())

    def getSort(self):
        """
            :return: The :py:class:`Sort` of this term.
        """
        return _sort(self.tm, self.cterm.getSort())

    def substitute(self, term_or_list_1, term_or_list_2):
        """
            :return: The result of simultaneously replacing the term(s) stored
                     in ``term_or_list_1`` by the term(s) stored in
                     ``term_or_list_2`` in this term.

            .. note::

                This replacement is applied during a pre-order traversal and
                only once to the term. It is not run until fix point. In the
                case that terms contains duplicates, the replacement earliest
                in the list takes priority. For example, calling substitute on
                ``f(x,y)`` with

                .. code:: python

                    term_or_list_1 = [ x, z ], term_or_list_2 = [ g(z), w ]

                results in the term ``f(g(z),y)``.
      """
        # lists for substitutions
        cdef vector[c_Term] ces
        cdef vector[c_Term] creplacements

        if isinstance(term_or_list_1, list):
            # call the API substitute method with lists
            assert isinstance(term_or_list_2, list)
            es = term_or_list_1
            replacements = term_or_list_2
            if len(es) != len(replacements):
                raise RuntimeError(
                    "Expecting list inputs to substitute to have the same "
                    "length but got: {} and {}".format(
                      len(es), len(replacements)))

            for e, r in zip(es, replacements):
                ces.push_back((<Term?> e).cterm)
                creplacements.push_back((<Term?> r).cterm)
            return _term(self.tm, self.cterm.substitute(ces, creplacements))
        # call the API substitute method with single terms
        return _term(
            self.tm,
            self.cterm.substitute(
              (<Term?> term_or_list_1).cterm, (<Term?> term_or_list_2).cterm))

    def hasOp(self):
        """
            :return: True iff this term has an operator.
        """
        return self.cterm.hasOp()

    def getOp(self):
        """
            :return: The :py:class:`Op` used to create this Term.

            .. note::

                This is safe to call when :py:meth:`hasOp()` returns True.
        """
        cdef Op op = Op(self.tm)
        op.cop = self.cterm.getOp()
        return op

    def hasSymbol(self):
        """
            :return: True iff this term has a symbol.
        """
        return self.cterm.hasSymbol()

    def getSymbol(self):
        """
            ..note:: Asserts :py:meth:`hasSymbol()`.

            :return: The raw symbol of the term.
        """
        return self.cterm.getSymbol().decode()

    def isNull(self):
        """
            :return: True iff this term is a null term.
        """
        return self.cterm.isNull()

    def notTerm(self):
        """
          Boolean negation.

          :return: The Boolean negation of this term.
        """
        return _term(self.tm, self.cterm.notTerm())

    def andTerm(self, Term t):
        """
            Boolean and.

            :param t: A Boolean term.
            :return: The conjunction of this term and the given term.
        """
        return _term(self.tm, self.cterm.andTerm((<Term> t).cterm))

    def orTerm(self, Term t):
        """
           Boolean or.

           :param t: A Boolean term.
           :return: The disjunction of this term and the given term.
        """
        return _term(self.tm, self.cterm.orTerm(t.cterm))

    def xorTerm(self, Term t):
        """
           Boolean exclusive or.

           :param t: A Boolean term.
           :return: The exclusive disjunction of this term and the given term.
        """
        return _term(self.tm, self.cterm.xorTerm(t.cterm))

    def eqTerm(self, Term t):
        """
           Equality

           :param t: A Boolean term.
           :return: The Boolean equivalence of this term and the given term.
        """
        return _term(self.tm, self.cterm.eqTerm(t.cterm))

    def impTerm(self, Term t):
        """
           Boolean Implication.

           :param t: A Boolean term.
           :return: The implication of this term and the given term.
        """
        return _term(self.tm, self.cterm.impTerm(t.cterm))

    def iteTerm(self, Term then_t, Term else_t):
        """
           If-then-else with this term as the Boolean condition.

           :param then_t: The `then` term.
           :param else_t: The `else` term.
           :return: The if-then-else term with this term as the Boolean
                    condition.
        """
        return _term(self.tm, self.cterm.iteTerm(then_t.cterm, else_t.cterm))

    def isConstArray(self):
        """
            :return: True iff this term is a constant array.
        """
        return self.cterm.isConstArray()

    def getConstArrayBase(self):
        """
           .. note:: Asserts :py:meth:`isConstArray()`.

           :return: The base (element stored at all indicies) of this constant
                    array.
        """
        return _term(self.tm, self.cterm.getConstArrayBase())

    def isBooleanValue(self):
        """
            :return: True iff this term is a Boolean value.
        """
        return self.cterm.isBooleanValue()

    def getBooleanValue(self):
        """
           .. note:: Asserts :py:meth:`isBooleanValue()`

           :return: The representation of a Boolean value as a native Boolean
                    value.
        """
        return self.cterm.getBooleanValue()

    def isStringValue(self):
        """
            :return: True iff this term is a string value.
        """
        return self.cterm.isStringValue()

    def getStringValue(self):
        """
            .. note:: Asserts :py:meth:`isStringValue()`.

            .. note::

                This function is not to be confused with :py:meth:`__str__()`
                which returns the term in some string representation, whatever
                data it may hold.

            :return: The string term as a native string value.
        """
        cdef c_u32string s = self.cterm.getU32StringValue()
        cdef Py_ssize_t n = s.size()

        if n == 0:
            return u""

        return PyUnicode_FromKindAndData(PyUnicode_4BYTE_KIND, <const void*>&s[0], n)


    def getRealOrIntegerValueSign(self):
        """
            Get integer or real value sign. Must be called on integer or real
            values, or otherwise an exception is thrown.

            :return: 0 if this term is zero, -1 if this term is a negative real
                     or integer value, 1 if this term is a positive real or
                     integer value.
        """
        return self.cterm.getRealOrIntegerValueSign()

    def isIntegerValue(self):
        """
            :return: True iff this term is an integer value.
        """
        return self.cterm.isIntegerValue()

    def getIntegerValue(self):
        """
           .. note:: Asserts :py:meth:`isIntegerValue()`.

           :return: The integer term as a native python integer.
        """
        return int(self.cterm.getIntegerValue().decode())

    def isFloatingPointPosZero(self):
        """
            :return: True iff the term is the floating-point value for positive
                     zero.
        """
        return self.cterm.isFloatingPointPosZero()

    def isFloatingPointNegZero(self):
        """
            :return: True iff the term is the floating-point value for negative
                     zero.
        """
        return self.cterm.isFloatingPointNegZero()

    def isFloatingPointPosInf(self):
        """
            :return: True iff the term is the floating-point value for positive
                     infinity.
         """
        return self.cterm.isFloatingPointPosInf()

    def isFloatingPointNegInf(self):
        """
            :return: True iff the term is the floating-point value for negative
                     infinity.
        """
        return self.cterm.isFloatingPointNegInf()

    def isFloatingPointNaN(self):
        """
            :return: True iff the term is the floating-point value for not a
                     number.
        """
        return self.cterm.isFloatingPointNaN()

    def isFloatingPointValue(self):
        """
            :return: True iff this term is a floating-point value.
        """
        return self.cterm.isFloatingPointValue()

    def getFloatingPointValue(self):
        """
           .. note:: Asserts :py:meth:`isFloatingPointValue()`.

           :return: The representation of a floating-point value as a tuple of
                    the exponent width, the significand width and a bit-vector
                    value.
        """
        cdef c_tuple[uint32_t, uint32_t, c_Term] t = \
            self.cterm.getFloatingPointValue()
        return (get0(t), get1(t), _term(self.tm, get2(t)))

    def isSetValue(self):
        r"""
            A term is a set value if it is considered to be a (canonical)
            constant set value.  A canonical set value is one whose AST is:

            .. code:: smtlib

                (set.union
                    (set.singleton c1) ...
                    (set.union (set.singleton c_{n-1}) (set.singleton c_n))))

            where :math:`c_1 \dots c_n` are values ordered by id such that
            :math:`c_1 > \cdots > c_n`.

            .. note::
                A universe set term
                (kind :py:obj:`SET_UNIVERSE <Kind.SET_UNIVERSE>`)
                is not considered to be a set value.

            :return: True if the term is a set value.
        """
        return self.cterm.isSetValue()

    def getSetValue(self):
        """
           .. note:: Asserts :py:meth:`isSetValue()`.

           :return: The representation of a set value as a set of terms.
        """
        elems = set()
        for e in self.cterm.getSetValue():
            elems.add(_term(self.tm, e))
        return elems

    def isSequenceValue(self):
        """
            :return: True iff this term is a sequence value.
        """
        return self.cterm.isSequenceValue()

    def getSequenceValue(self):
        """
            .. note:: Asserts :py:meth:`isSequenceValue()`.

            .. note::

                It is usually necessary for sequences to call
                :py:meth:`Solver.simplify()` to turn a sequence that is
                constructed by, e.g., concatenation of unit sequences, into a
                sequence value.

            :return: The representation of a sequence value as a vector of
                     terms.
        """
        elems = []
        for e in self.cterm.getSequenceValue():
            elems.append(_term(self.tm, e))
        return elems

    def isCardinalityConstraint(self):
        """
            :return: True if the term is a cardinality constraint.

            .. warning::

                This function is experimental and may change in future versions.
        """
        return self.cterm.isCardinalityConstraint()

    def getCardinalityConstraint(self):
        """
            .. note:: Asserts :py:meth:`isCardinalityConstraint()`.

            :return: The sort the cardinality constraint is for and its upper
                     bound.

            .. warning::

                This function is experimental and may change in future versions.
        """
        cdef pair[c_Sort, uint32_t] p
        p = self.cterm.getCardinalityConstraint()
        return (_sort(self.tm, p.first), p.second)

    def isRealAlgebraicNumber(self):
        """
            :return: True if the term is a real algebraic number.

            .. warning::

                This function is experimental and may change in future versions.
        """
        return self.cterm.isRealAlgebraicNumber()


    def getRealAlgebraicNumberDefiningPolynomial(self, Term v):
        """
            .. note:: Asserts :py:meth:`isRealAlgebraicNumber()`.

           :param v: The variable over which to express the polynomial
           :return: The defining polynomial for the real algebraic number, expressed in
                    terms of the given variable.
        """
        return _term(
            self.tm,
            self.cterm.getRealAlgebraicNumberDefiningPolynomial(v.cterm))

    def getRealAlgebraicNumberLowerBound(self):
        """
            .. note:: Asserts :py:meth:`isRealAlgebraicNumber()`.

          :return: The lower bound for the value of the real algebraic number.
        """
        return _term(
            self.tm,
            self.cterm.getRealAlgebraicNumberLowerBound())

    def getRealAlgebraicNumberUpperBound(self):
        """
            .. note:: Asserts :py:meth:`isRealAlgebraicNumber()`.

          :return: The upper bound for the value of the real algebraic number.
        """
        return _term(
            self.tm,
            self.cterm.getRealAlgebraicNumberUpperBound())

    def isSkolem(self):
        """
            :return: True if the term is a skolem.

            .. warning::

                This function is experimental and may change in future versions.
        """
        return self.cterm.isSkolem()

    def getSkolemId(self):
        """
            Get skolem identifier of this term.
            .. note:: Asserts :py:meth:`isSkolem()`.

            .. warning::

                This function is experimental and may change in future versions.

            :return: The skolem identifier of this term.
        """
        return SkolemId(<int> self.cterm.getSkolemId())

    def getSkolemIndices(self):
        """
            .. note:: Asserts :py:meth:`isSkolem()`.

            .. warning::

                This function is experimental and may change in future versions.

           :return: The skolem indices of this term. This is list of terms that
                    the skolem function is indexed by. For example, the array
                    diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two
                    arrays.
        """
        indices = []
        for i in self.cterm.getSkolemIndices():
            indices.append(_term(self.tm, i))
        return indices

    def isUninterpretedSortValue(self):
        """
            :return: True iff this term is a value from an uninterpreted sort.
        """
        return self.cterm.isUninterpretedSortValue()

    def getUninterpretedSortValue(self):
        """
           .. note:: Asserts :py:meth:`isUninterpretedSortValue()`.

           :return: The representation of an uninterpreted value as a pair of
                    its sort and its index.
        """
        return self.cterm.getUninterpretedSortValue()

    def isTupleValue(self):
        """
            :return: True iff this term is a tuple value.
        """
        return self.cterm.isTupleValue()

    def isRoundingModeValue(self):
        """
            :return: True if the term is a floating-point rounding mode
                     value.
        """
        return self.cterm.isRoundingModeValue()

    def getRoundingModeValue(self):
        """
            .. note:: Asserts :py:meth:`isRoundingModeValue()`.

            :return: The floating-point rounding mode value held by the term.
        """
        return RoundingMode(<int> self.cterm.getRoundingModeValue())

    def getTupleValue(self):
        """
           .. note:: Asserts :py:meth:`isTupleValue()`.

           :return: The representation of a tuple value as a vector of terms.
        """
        elems = []
        for e in self.cterm.getTupleValue():
            elems.append(_term(self.tm, e))
        return elems

    def isRealValue(self):
        """
            :return: True iff this term is a rational value.

            .. note::

                A term of kind :py:obj:`PI <Kind.PI>` is not considered
                to be a real value.

        """
        return self.cterm.isRealValue()

    def getRealValue(self):
        """
           .. note:: Asserts :py:meth:`isRealValue()`.

           :return: The representation of a rational value as a python Fraction.
        """
        return Fraction(self.cterm.getRealValue().decode())

    def isBitVectorValue(self):
        """
            :return: True iff this term is a bit-vector value.
        """
        return self.cterm.isBitVectorValue()

    def getBitVectorValue(self, base = 2):
        """
           .. note:: Asserts :py:meth:`isBitVectorValue()`.

           Supported bases are 2 (bit string), 10 (decimal string) or 16
           (hexdecimal string).

           :return: The representation of a bit-vector value in string
                    representation.
        """
        return self.cterm.getBitVectorValue(base).decode()

    def isFiniteFieldValue(self):
        """
            :return: True iff this term is a finite field value.
        """
        return self.cterm.isFiniteFieldValue()

    def getFiniteFieldValue(self):
        """
           .. note:: Asserts :py:meth:`isFiniteFieldValue()`.

           .. note:: Uses the integer representative of smallest absolute value.

           :return: The representation of a finite field value as an integer.
        """
        return int(self.cterm.getFiniteFieldValue().decode())

    def toPythonObj(self):
        """
            Converts a constant value Term to a Python object.

            Currently supports:

            - **Boolean:** Returns a Python bool
            - **Int    :** Returns a Python int
            - **Real   :** Returns a Python Fraction
            - **BV     :** Returns a Python int (treats BV as unsigned)
            - **FF     :** Returns a Python int (gives the FF integer representative of smallest absolute value)
            - **String :** Returns a Python Unicode string
            - **Array  :** Returns a Python dict mapping indices to values. The constant base is returned as the default value.

        """

        if self.isBooleanValue():
            return self.getBooleanValue()
        elif self.isIntegerValue():
            return self.getIntegerValue()
        elif self.isRealValue():
            return self.getRealValue()
        elif self.isBitVectorValue():
            return int(self.getBitVectorValue(), 2)
        elif self.isFiniteFieldValue():
            return self.getFiniteFieldValue()
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

# ----------------------------------------------------------------------------
# Proof
# ----------------------------------------------------------------------------

cdef class Proof:
    """
        A cvc5 proof.  Proofs are trees and every proof object corresponds to the
        root step of a proof.  The branches of the root step are the premises of
        the step.

        Wrapper class for :cpp:class:`cvc5::Proof`.
    """
    cdef c_Proof cproof
    cdef TermManager tm

    def __eq__(self, Proof other):
        return self.cproof == other.cproof

    def __ne__(self, Proof other):
        return self.cproof != other.cproof

    def __hash__(self):
        return cproofhash(self.cproof)

    def getRule(self):
        """
            :return: The proof rule used by the root step of the proof.
        """
        return ProofRule(<int> self.cproof.getRule())

    def getRewriteRule(self):
        """
            :return: The proof rewrite rule used by the root step of the proof.
                     Raises an exception if `getRule()` does not return
                     `DSL_REWRITE` or `THEORY_REWRITE`.
        """
        return ProofRewriteRule(<int> self.cproof.getRewriteRule())

    def getResult(self):
        """
            :return: The conclusion of the root step of the proof.
        """
        return _term(self.tm, self.cproof.getResult())

    def getChildren(self):
        """
            :return: The premises of the root step of the proof.
        """
        proofs = []
        for p in self.cproof.getChildren():
            proofs.append(_proof(self.tm, p))
        return proofs

    def getArguments(self):
        """
            :return: The arguments of the root step of the proof as a vector of terms.
                    Some of those terms might be strings.
        """
        args = []
        for a in self.cproof.getArguments():
            args.append(_term(self.tm, a))
        return args


cdef public api:
    string cy_call_string_func(object self, string method, string *error):
        try:
            func = getattr(self, method.decode())
            return func().encode()
        except Exception as e:
            error[0] = traceback.format_exc().encode()
        return b""

    vector[c_Term] cy_call_vec_term_func(object self, string method, string *error):
        cdef vector[c_Term] result
        try:
            func = getattr(self, method.decode())
            terms = func()
            for t in terms:
                result.push_back((<Term?> t).cterm)
        except Exception as e:
            error[0] = traceback.format_exc().encode()
        return result


    void cy_call_void_func_term(object self, string method, const c_Term& t, string *error):
        try:
            func = getattr(self, method.decode())
            func(_term(self._Plugin__term_manager(), t))
        except Exception as e:
            error[0] = traceback.format_exc().encode()

