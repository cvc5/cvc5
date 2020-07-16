# import dereference and increment operators
from cython.operator cimport dereference as deref, preincrement as inc
from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libcpp.string cimport string
from libcpp.vector cimport vector
from libcpp.pair cimport pair
from cvc4kinds cimport Kind


cdef extern from "<iostream>" namespace "std":
    cdef cppclass ostream:
        pass
    ostream cout


cdef extern from "api/cvc4cpp.h" namespace "CVC4":
    cdef cppclass Options:
        pass


cdef extern from "api/cvc4cpp.h" namespace "CVC4::api":
    cdef cppclass Datatype:
        Datatype() except +
        DatatypeConstructor operator[](size_t idx) except +
        DatatypeConstructor operator[](const string& name) except +
        DatatypeConstructor getConstructor(const string& name) except +
        Term getConstructorTerm(const string& name) except +
        size_t getNumConstructors() except +
        bint isParametric() except +
        string toString() except +
        cppclass const_iterator:
            const_iterator() except +
            bint operator==(const const_iterator& it) except +
            bint operator!=(const const_iterator& it) except +
            const_iterator& operator++();
            const DatatypeConstructor& operator*() except +
        const_iterator begin() except +
        const_iterator end() except +


    cdef cppclass DatatypeConstructor:
        DatatypeConstructor() except +
        DatatypeSelector operator[](size_t idx) except +
        DatatypeSelector operator[](const string& name) except +
        string getName() except +
        Term getConstructorTerm() except +
        Term getTesterTerm() except +
        size_t getNumSelectors() except +
        DatatypeSelector getSelector(const string& name) except +
        Term getSelectorTerm(const string& name) except +
        string toString() except +
        cppclass const_iterator:
            const_iterator() except +
            bint operator==(const const_iterator& it) except +
            bint operator!=(const const_iterator& it) except +
            const_iterator& operator++();
            const DatatypeSelector& operator*() except +
        const_iterator begin() except +
        const_iterator end() except +


    cdef cppclass DatatypeConstructorDecl:
        void addSelector(const string& name, Sort sort) except +
        void addSelectorSelf(const string& name) except +
        string toString() except +


    cdef cppclass DatatypeDecl:
        void addConstructor(const DatatypeConstructorDecl& ctor) except +
        size_t getNumConstructors() except +
        bint isParametric() except +
        string toString() except +


    cdef cppclass DatatypeSelector:
        DatatypeSelector() except +
        string getName() except +
        Term getSelectorTerm() except +
        Sort getRangeSort() except +
        string toString() except +


    cdef cppclass Op:
        Op() except +
        bint operator==(const Op&) except +
        bint operator!=(const Op&) except +
        Kind getKind() except +
        Sort getSort() except +
        bint isNull() except +
        T getIndices[T]() except +
        string toString() except +

    cdef cppclass OpHashFunction:
        OpHashFunction() except +
        size_t operator()(const Op & o) except +


    cdef cppclass Result:
        Result() except+
        bint isNull() except +
        bint isSat() except +
        bint isUnsat() except +
        bint isSatUnknown() except +
        bint isEntailed() except +
        bint isNotEntailed() except +
        bint isEntailmentUnknown() except +
        bint operator==(const Result& r) except +
        bint operator!=(const Result& r) except +
        string getUnknownExplanation() except +
        string toString() except +


    cdef cppclass RoundingMode:
        pass


    cdef cppclass Solver:
        Solver(Options*) except +
        Sort getBooleanSort() except +
        Sort getIntegerSort() except +
        Sort getRealSort() except +
        Sort getRegExpSort() except +
        Sort getRoundingmodeSort() except +
        Sort getStringSort() except +
        Sort mkArraySort(Sort indexSort, Sort elemSort) except +
        Sort mkBitVectorSort(uint32_t size) except +
        Sort mkFloatingPointSort(uint32_t exp, uint32_t sig) except +
        Sort mkDatatypeSort(DatatypeDecl dtypedecl) except +
        Sort mkFunctionSort(Sort domain, Sort codomain) except +
        Sort mkFunctionSort(const vector[Sort]& sorts, Sort codomain) except +
        Sort mkParamSort(const string& symbol) except +
        Sort mkPredicateSort(const vector[Sort]& sorts) except +
        Sort mkRecordSort(const vector[pair[string, Sort]]& fields) except +
        Sort mkSetSort(Sort elemSort) except +
        Sort mkSequenceSort(Sort elemSort) except +
        Sort mkUninterpretedSort(const string& symbol) except +
        Sort mkSortConstructorSort(const string& symbol, size_t arity) except +
        Sort mkTupleSort(const vector[Sort]& sorts) except +
        Term mkTerm(Op op) except +
        Term mkTerm(Op op, const vector[Term]& children) except +
        Op mkOp(Kind kind) except +
        Op mkOp(Kind kind, Kind k) except +
        Op mkOp(Kind kind, const string& arg) except +
        Op mkOp(Kind kind, uint32_t arg) except +
        Op mkOp(Kind kind, uint32_t arg1, uint32_t arg2) except +
        Term mkTrue() except +
        Term mkFalse() except +
        Term mkBoolean(bint val) except +
        Term mkPi() except +
        Term mkReal(const string& s) except +
        Term mkRegexpEmpty() except +
        Term mkRegexpSigma() except +
        Term mkEmptySet(Sort s) except +
        Term mkSepNil(Sort sort) except +
        Term mkString(const string& s) except +
        Term mkString(const vector[unsigned]& s) except +
        Term mkEmptySequence(Sort sort) except +
        Term mkUniverseSet(Sort sort) except +
        Term mkBitVector(uint32_t size) except +
        Term mkBitVector(uint32_t size, uint64_t val) except +
        Term mkBitVector(const string& s) except +
        Term mkBitVector(const string& s, uint32_t base) except +
        Term mkConstArray(Sort sort, Term val) except +
        Term mkPosInf(uint32_t exp, uint32_t sig) except +
        Term mkNegInf(uint32_t exp, uint32_t sig) except +
        Term mkNaN(uint32_t exp, uint32_t sig) except +
        Term mkPosZero(uint32_t exp, uint32_t sig) except +
        Term mkNegZero(uint32_t exp, uint32_t sig) except +
        Term mkRoundingMode(RoundingMode rm) except +
        Term mkUninterpretedConst(Sort sort, int32_t index) except +
        Term mkAbstractValue(const string& index) except +
        Term mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) except +
        Term mkConst(Sort sort, const string& symbol) except +
        # default value for symbol defined in cvc4cpp.h
        Term mkConst(Sort sort) except +
        Term mkVar(Sort sort, const string& symbol) except +
        DatatypeConstructorDecl mkDatatypeConstructorDecl(const string& name) except +
        DatatypeDecl mkDatatypeDecl(const string& name) except +
        DatatypeDecl mkDatatypeDecl(const string& name, bint isCoDatatype) except +
        DatatypeDecl mkDatatypeDecl(const string& name, Sort param) except +
        DatatypeDecl mkDatatypeDecl(const string& name, Sort param, bint isCoDatatype) except +
        DatatypeDecl mkDatatypeDecl(const string& name, vector[Sort]& params) except +
        DatatypeDecl mkDatatypeDecl(const string& name, vector[Sort]& params, bint isCoDatatype) except +
        # default value for symbol defined in cvc4cpp.h
        Term mkVar(Sort sort) except +
        Term simplify(const Term& t) except +
        void assertFormula(Term term) except +
        Result checkSat() except +
        Result checkSatAssuming(const vector[Term]& assumptions) except +
        Result checkEntailed(const vector[Term]& assumptions) except +
        Sort declareDatatype(const string& symbol, const vector[DatatypeConstructorDecl]& ctors)
        Term declareFun(const string& symbol, Sort sort) except +
        Term declareFun(const string& symbol, const vector[Sort]& sorts, Sort sort) except +
        Sort declareSort(const string& symbol, uint32_t arity) except +
        Term defineFun(const string& symbol, const vector[Term]& bound_vars,
                       Sort sort, Term term, bint glbl) except +
        Term defineFun(Term fun, const vector[Term]& bound_vars, Term term, bint glbl) except +
        Term defineFunRec(const string& symbol, const vector[Term]& bound_vars,
                          Sort sort, Term term, bint glbl) except +
        Term defineFunRec(Term fun, const vector[Term]& bound_vars,
                          Term term, bint glbl) except +
        Term defineFunsRec(vector[Term]& funs, vector[vector[Term]]& bound_vars,
                           vector[Term]& terms, bint glbl) except +
        vector[Term] getAssertions() except +
        vector[pair[Term, Term]] getAssignment() except +
        string getInfo(const string& flag) except +
        string getOption(string& option) except +
        vector[Term] getUnsatAssumptions() except +
        vector[Term] getUnsatCore() except +
        Term getValue(Term term) except +
        vector[Term] getValue(const vector[Term]& terms) except +
        Term getSeparationHeap() except +
        Term getSeparationNilTerm() except +
        void pop(uint32_t nscopes) except +
        void printModel(ostream& out)
        void push(uint32_t nscopes) except +
        void reset() except +
        void resetAssertions() except +
        void setInfo(string& keyword, const string& value) except +
        void setLogic(const string& logic) except +
        void setOption(const string& option, const string& value) except +


    cdef cppclass Sort:
        Sort() except +
        bint operator==(const Sort&) except +
        bint operator!=(const Sort&) except +
        bint operator<(const Sort&) except +
        bint operator>(const Sort&) except +
        bint operator<=(const Sort&) except +
        bint operator>=(const Sort&) except +
        bint isBoolean() except +
        bint isInteger() except +
        bint isReal() except +
        bint isString() except +
        bint isRegExp() except +
        bint isRoundingMode() except +
        bint isBitVector() except +
        bint isFloatingPoint() except +
        bint isDatatype() except +
        bint isParametricDatatype() except +
        bint isConstructor() except +
        bint isSelector() except +
        bint isTester() except +
        bint isFunction() except +
        bint isPredicate() except +
        bint isTuple() except +
        bint isRecord() except +
        bint isArray() except +
        bint isSet() except +
        bint isSequence() except +
        bint isUninterpretedSort() except +
        bint isSortConstructor() except +
        bint isFirstClass() except +
        bint isFunctionLike() except +
        bint isSubsortOf(Sort s) except +
        bint isComparableTo(Sort s) except +
        Datatype getDatatype() except +
        Sort instantiate(const vector[Sort]& params) except +
        size_t getConstructorArity() except +
        vector[Sort] getConstructorDomainSorts() except +
        Sort getConstructorCodomainSort() except +
        size_t getFunctionArity() except +
        vector[Sort] getFunctionDomainSorts() except +
        Sort getFunctionCodomainSort() except +
        Sort getArrayIndexSort() except +
        Sort getArrayElementSort() except +
        Sort getSetElementSort() except +
        Sort getSequenceElementSort() except +
        string getUninterpretedSortName() except +
        bint isUninterpretedSortParameterized() except +
        vector[Sort] getUninterpretedSortParamSorts() except +
        string getSortConstructorName() except +
        size_t getSortConstructorArity() except +
        uint32_t getBVSize() except +
        uint32_t getFPExponentSize() except +
        uint32_t getFPSignificandSize() except +
        vector[Sort] getDatatypeParamSorts() except +
        size_t getDatatypeArity() except +
        size_t getTupleLength() except +
        vector[Sort] getTupleSorts() except +
        string toString() except +

    cdef cppclass SortHashFunction:
        SortHashFunction() except +
        size_t operator()(const Sort & s) except +

    cdef cppclass Term:
        Term()
        bint operator==(const Term&) except +
        bint operator!=(const Term&) except +
        Kind getKind() except +
        Sort getSort() except +
        Term substitute(const vector[Term] es, const vector[Term] & reps) except +
        bint hasOp() except +
        Op getOp() except +
        bint isNull() except +
        bint isConst() except +
        Term getConstArrayBase() except +
        vector[Term] getConstSequenceElements() except +
        Term notTerm() except +
        Term andTerm(const Term& t) except +
        Term orTerm(const Term& t) except +
        Term xorTerm(const Term& t) except +
        Term eqTerm(const Term& t) except +
        Term impTerm(const Term& t) except +
        Term iteTerm(const Term& then_t, const Term& else_t) except +
        string toString() except +
        cppclass const_iterator:
            const_iterator() except +
            bint operator==(const const_iterator& it) except +
            bint operator!=(const const_iterator& it) except +
            const_iterator& operator++();
            Term operator*() except +
        const_iterator begin() except +
        const_iterator end() except +

    cdef cppclass TermHashFunction:
        TermHashFunction() except +
        size_t operator()(const Term & t) except +


cdef extern from "api/cvc4cpp.h" namespace "CVC4::api::RoundingMode":
    cdef RoundingMode ROUND_NEAREST_TIES_TO_EVEN,
    cdef RoundingMode ROUND_TOWARD_POSITIVE,
    cdef RoundingMode ROUND_TOWARD_NEGATIVE,
    cdef RoundingMode ROUND_TOWARD_ZERO,
    cdef RoundingMode ROUND_NEAREST_TIES_TO_AWAY
