# import dereference and increment operators
from cython.operator cimport dereference as deref, preincrement as inc
from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libc.stddef cimport wchar_t
from libcpp.map cimport map as c_map
from libcpp.set cimport set
from libcpp.string cimport string
from libcpp.vector cimport vector
from libcpp.map cimport map
from libcpp.pair cimport pair
from cvc5kinds cimport Kind
from cvc5sortkinds cimport SortKind
from cvc5types cimport BlockModelsMode, LearnedLitType, ProofComponent, RoundingMode, UnknownExplanation


cdef extern from "<iostream>" namespace "std":
    cdef cppclass ostream:
        pass
    ostream cout


cdef extern from "<functional>" namespace "std" nogil:
    cdef cppclass hash[T]:
        hash()
        size_t operator()(T t)

cdef extern from "<optional>" namespace "std" nogil:
    # The std::optional wrapper would be available as cpplib.optional with
    # cython 3.0.0a10 (Jan 2022). Until this version is widely available, we
    # wrap it manually.
    cdef cppclass optional[T]:
        bint has_value()
        T& value()

cdef extern from "<string>" namespace "std":
    cdef cppclass wstring:
        wstring() except +
        wstring(const wchar_t*, size_t) except +
        const wchar_t* data() except +
        size_t size() except +

cdef extern from "<tuple>" namespace "std" nogil:
    cdef cppclass tuple[T, U, S]:
        pass

cdef extern from "<tuple>" namespace "std":
    uint32_t get0 "std::get<0>"(tuple[uint32_t,uint32_t,Term]) except +
    uint32_t get1 "std::get<1>"(tuple[uint32_t,uint32_t,Term]) except +
    Term get2 "std::get<2>"(tuple[uint32_t,uint32_t,Term]) except +

cdef extern from "<cvc5/cvc5.h>" namespace "cvc5":
    cdef cppclass Options:
        pass


cdef extern from "<cvc5/cvc5.h>" namespace "cvc5":
    cdef cppclass Datatype:
        Datatype() except +
        DatatypeConstructor operator[](size_t idx) except +
        DatatypeConstructor operator[](const string& name) except +
        DatatypeConstructor getConstructor(const string& name) except +
        DatatypeSelector getSelector(const string& name) except +
        string getName() except +
        size_t getNumConstructors() except +
        vector[Sort] getParameters() except +
        bint isParametric() except +
        bint isCodatatype() except +
        bint isTuple() except +
        bint isRecord() except +
        bint isFinite() except +
        bint isWellFounded() except +
        bint isNull() except +
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
        Term getTerm() except +
        Term getInstantiatedTerm(const Sort& retSort) except +
        Term getTesterTerm() except +
        size_t getNumSelectors() except +
        DatatypeSelector getSelector(const string& name) except +
        bint isNull() except +
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
        void addSelectorUnresolved(const string& name, const string& unresDatatypeName) except +
        bint isNull() except +
        string toString() except +


    cdef cppclass DatatypeDecl:
        void addConstructor(const DatatypeConstructorDecl& ctor) except +
        size_t getNumConstructors() except +
        bint isParametric() except +
        string toString() except +
        string getName() except +
        bint isNull() except +


    cdef cppclass DatatypeSelector:
        DatatypeSelector() except +
        string getName() except +
        Term getTerm() except +
        Term getUpdaterTerm() except +
        Sort getCodomainSort() except +
        bint isNull() except +
        string toString() except +


    cdef cppclass Op:
        Op() except +
        bint operator==(const Op&) except +
        bint operator!=(const Op&) except +
        Kind getKind() except +
        Sort getSort() except +
        bint isNull() except +
        bint isIndexed() except +
        size_t getNumIndices() except +
        Term operator[](size_t i) except +
        string toString() except +

    cdef cppclass OpHashFunction:
        OpHashFunction() except +
        size_t operator()(const Op & o) except +

    cdef cppclass OptionInfo:
        string name
        vector[string] aliases
        bint setByUser
        bint boolValue() except +
        string stringValue() except +
        int intValue() except +
        int uintValue() except +
        float doubleValue() except +
        cppclass VoidInfo:
            pass
        cppclass ValueInfo[T]:
            T defaultValue
            T currentValue
        cppclass NumberInfo[T]:
            T defaultValue
            T currentValue
            optional[T] minimum
            optional[T] maximum
        cppclass ModeInfo:
            string defaultValue
            string currentValue
            vector[string] modes

        cppclass OptionInfoVariant:
            pass

        OptionInfoVariant valueInfo
        string toString() except +


cdef extern from "<variant>" namespace "std":
    # cython has no support for variadic templates yet, see
    # https://github.com/cython/cython/issues/1611
    bint holds "std::holds_alternative"[T](OptionInfo.OptionInfoVariant v) except +
    T getVariant "std::get"[T](OptionInfo.OptionInfoVariant v) except +

cdef extern from "<cvc5/cvc5.h>" namespace "cvc5":
    cdef cppclass Result:
        Result() except+
        bint isNull() except +
        bint isSat() except +
        bint isUnsat() except +
        bint isUnknown() except +
        bint operator==(const Result& r) except +
        bint operator!=(const Result& r) except +
        UnknownExplanation getUnknownExplanation() except +
        string toString() except +

    cdef cppclass SynthResult:
        SynthResult() except+
        bint isNull() except +
        bint hasSolution() except +
        bint hasNoSolution() except +
        bint isUnknown() except +
        string toString() except +

    cdef cppclass Solver:
        Solver() except +
        Sort getBooleanSort() except +
        Sort getIntegerSort() except +
        Sort getRealSort() except +
        Sort getRegExpSort() except +
        Sort getRoundingModeSort() except +
        Sort getStringSort() except +
        Sort mkArraySort(Sort indexSort, Sort elemSort) except +
        Sort mkBitVectorSort(uint32_t size) except +
        Sort mkFloatingPointSort(uint32_t exp, uint32_t sig) except +
        Sort mkFiniteFieldSort(const string& size) except +
        Sort mkDatatypeSort(DatatypeDecl dtypedecl) except +
        vector[Sort] mkDatatypeSorts(const vector[DatatypeDecl]& dtypedecls) except +
        Sort mkFunctionSort(const vector[Sort]& sorts, Sort codomain) except +
        Sort mkParamSort() except +
        Sort mkParamSort(const string& symbol) except +
        Sort mkPredicateSort(const vector[Sort]& sorts) except +
        Sort mkRecordSort(const vector[pair[string, Sort]]& fields) except +
        Sort mkSetSort(Sort elemSort) except +
        Sort mkBagSort(Sort elemSort) except +
        Sort mkSequenceSort(Sort elemSort) except +
        Sort mkAbstractSort(SortKind kind) except +
        Sort mkUninterpretedSort() except +
        Sort mkUninterpretedSort(const string& symbol) except +
        Sort mkUnresolvedDatatypeSort(const string& symbol, size_t arity) except +
        Sort mkUninterpretedSortConstructorSort(size_t arity) except +
        Sort mkUninterpretedSortConstructorSort(size_t arity, const string& symbol) except +
        Sort mkTupleSort(const vector[Sort]& sorts) except +
        Term mkTerm(Op op) except +
        Term mkTerm(Op op, const vector[Term]& children) except +
        Term mkTuple(const vector[Term]& terms) except +
        Op mkOp(Kind kind) except +
        Op mkOp(Kind kind, const string& arg) except +
        Op mkOp(Kind kind, const vector[uint32_t]& args) except +
        # Sygus related functions
        Grammar mkGrammar(const vector[Term]& boundVars, const vector[Term]& ntSymbols) except +
        Term declareSygusVar(const string& symbol, Sort sort) except +
        void addSygusConstraint(Term term) except +
        vector[Term] getSygusConstraints() except +
        void addSygusAssume(Term term) except +
        vector[Term] getSygusAssumptions() except +
        void addSygusInvConstraint(Term inv_f, Term pre_f, Term trans_f, Term post_f) except +
        Term synthFun(const string& symbol, const vector[Term]& bound_vars, Sort sort) except +
        Term synthFun(const string& symbol, const vector[Term]& bound_vars, Sort sort, Grammar grammar) except +
        SynthResult checkSynth() except +
        SynthResult checkSynthNext() except +
        Term getSynthSolution(Term t) except +
        vector[Term] getSynthSolutions(const vector[Term]& terms) except +
        # End of sygus related functions

        Term mkTrue() except +
        Term mkFalse() except +
        Term mkBoolean(bint val) except +
        Term mkPi() except +
        Term mkInteger(const uint64_t i) except +
        Term mkInteger(const string& s) except +
        Term mkReal(const string& s) except +
        Term mkRegexpAll() except +
        Term mkRegexpAllchar() except +
        Term mkRegexpNone() except +
        Term mkEmptySet(Sort s) except +
        Term mkEmptyBag(Sort s) except +
        Term mkSepEmp() except +
        Term mkSepNil(Sort sort) except +
        Term mkString(const string& s) except +
        Term mkString(const wstring& s) except +
        Term mkString(const string& s, bint useEscSequences) except +
        Term mkEmptySequence(Sort sort) except +
        Term mkUniverseSet(Sort sort) except +
        Term mkBitVector(uint32_t size) except +
        Term mkBitVector(uint32_t size, uint64_t val) except +
        Term mkBitVector(const string& s) except +
        Term mkBitVector(const string& s, uint32_t base) except +
        Term mkBitVector(uint32_t size, string& s, uint32_t base) except +
        Term mkFiniteFieldElem(const string& s, Sort sort) except +
        Term mkConstArray(Sort sort, Term val) except +
        Term mkFloatingPointPosInf(uint32_t exp, uint32_t sig) except +
        Term mkFloatingPointNegInf(uint32_t exp, uint32_t sig) except +
        Term mkFloatingPointNaN(uint32_t exp, uint32_t sig) except +
        Term mkFloatingPointPosZero(uint32_t exp, uint32_t sig) except +
        Term mkFloatingPointNegZero(uint32_t exp, uint32_t sig) except +
        Term mkRoundingMode(RoundingMode rm) except +
        Term mkFloatingPoint(uint32_t exp, uint32_t sig, const Term& val) except +
        Term mkFloatingPoint(const Term& arg0, const Term& arg1, const Term& arg2) except +
        Term mkCardinalityConstraint(Sort sort, int32_t index) except +
        Term mkConst(Sort sort, const string& symbol) except +
        # default value for symbol defined in cpp/cvc5.h
        Term mkConst(Sort sort) except +
        Term mkVar(Sort sort, const string& symbol) except +
        DatatypeConstructorDecl mkDatatypeConstructorDecl(const string& name) except +
        DatatypeDecl mkDatatypeDecl(const string& name) except +
        DatatypeDecl mkDatatypeDecl(const string& name, bint isCoDatatype) except +
        DatatypeDecl mkDatatypeDecl(const string& name, vector[Sort]& params) except +
        DatatypeDecl mkDatatypeDecl(const string& name, vector[Sort]& params, bint isCoDatatype) except +
        # default value for symbol defined in cpp/cvc5.h
        Term mkVar(Sort sort) except +
        Term simplify(const Term& t) except +
        void assertFormula(Term term) except +
        Result checkSat() except +
        Result checkSatAssuming(const vector[Term]& assumptions) except +
        Sort declareDatatype(const string& symbol, const vector[DatatypeConstructorDecl]& ctors)
        Term declareFun(const string& symbol, Sort sort) except +
        Term declareFun(const string& symbol, const vector[Sort]& sorts, Sort sort) except +
        Sort declareSort(const string& symbol, uint32_t arity) except +
        Term defineFun(const string& symbol, const vector[Term]& bound_vars,
                       Sort sort, Term term, bint glbl) except +
        Term defineFunRec(const string& symbol, const vector[Term]& bound_vars,
                          Sort sort, Term term, bint glbl) except +
        Term defineFunRec(Term fun, const vector[Term]& bound_vars,
                          Term term, bint glbl) except +
        Term defineFunsRec(vector[Term]& funs, vector[vector[Term]]& bound_vars,
                           vector[Term]& terms, bint glbl) except +
        string getProof(ProofComponent c) except +
        vector[Term] getLearnedLiterals(LearnedLitType type) except +
        vector[Term] getAssertions() except +
        string getInfo(const string& flag) except +
        string getOption(const string& option) except +
        vector[string] getOptionNames() except +
        OptionInfo getOptionInfo(const string& option) except +
        vector[Term] getUnsatAssumptions() except +
        vector[Term] getUnsatCore() except +
        map[Term,Term] getDifficulty() except +
        pair[Result, vector[Term]] getTimeoutCore() except +
        Term getValue(Term term) except +
        vector[Term] getValue(const vector[Term]& terms) except +
        Term getQuantifierElimination(const Term& q) except +
        Term getQuantifierEliminationDisjunct(const Term& q) except +
        vector[Term] getModelDomainElements(Sort sort) except +
        bint isModelCoreSymbol(Term v) except +
        string getModel(const vector[Sort]& sorts,
                        const vector[Term]& consts) except +
        void declareSepHeap(Sort locSort, Sort dataSort) except +
        Term getValueSepHeap() except +
        Term getValueSepNil() except +
        Term declarePool(const string& name, Sort sort, vector[Term]& initValue) except +
        void pop(uint32_t nscopes) except +
        void push(uint32_t nscopes) except +
        void reset() except +
        void resetAssertions() except +
        void setInfo(string& keyword, const string& value) except +
        void setLogic(const string& logic) except +
        void setOption(const string& option, const string& value) except +
        Term getInterpolant(const Term& conj) except +
        Term getInterpolant(const Term& conj, Grammar& grammar) except +
        Term getInterpolantNext() except +
        Term getAbduct(const Term& conj) except +
        Term getAbduct(const Term& conj, Grammar& grammar) except +
        Term getAbductNext() except +
        void blockModel() except +
        void blockModel(BlockModelsMode mode) except +
        void blockModelValues(const vector[Term]& terms) except +
        string getInstantiations() except +
        Statistics getStatistics() except +
        string getVersion() except +

    cdef cppclass Grammar:
        Grammar() except +
        Grammar(Solver* solver, vector[Term] boundVars, vector[Term] ntSymbols) except +
        void addRule(Term ntSymbol, Term rule) except +
        void addAnyConstant(Term ntSymbol) except +
        void addAnyVariable(Term ntSymbol) except +
        void addRules(Term ntSymbol, vector[Term] rules) except +
        string toString() except +

    cdef cppclass Sort:
        Sort() except +
        bint operator==(const Sort&) except +
        bint operator!=(const Sort&) except +
        bint operator<(const Sort&) except +
        bint operator>(const Sort&) except +
        bint operator<=(const Sort&) except +
        bint operator>=(const Sort&) except +
        SortKind getKind() except +
        bint hasSymbol() except +
        string getSymbol() except +
        bint isNull() except +
        bint isBoolean() except +
        bint isInteger() except +
        bint isReal() except +
        bint isString() except +
        bint isRegExp() except +
        bint isRoundingMode() except +
        bint isBitVector() except +
        bint isFloatingPoint() except +
        bint isDatatype() except +
        bint isDatatypeConstructor() except +
        bint isDatatypeSelector() except +
        bint isDatatypeTester() except +
        bint isDatatypeUpdater() except +
        bint isFunction() except +
        bint isPredicate() except +
        bint isTuple() except +
        bint isRecord() except +
        bint isArray() except +
        bint isFiniteField() except +
        bint isSet() except +
        bint isBag() except +
        bint isSequence() except +
        bint isAbstract() except +
        bint isUninterpretedSort() except +
        bint isUninterpretedSortConstructor() except +
        bint isInstantiated() except +
        Sort getUninterpretedSortConstructor() except +
        Datatype getDatatype() except +
        Sort instantiate(const vector[Sort]& params) except +
        vector[Sort] getInstantiatedParameters() except +
        Sort substitute(const Sort & es, const Sort & reps) except +
        Sort substitute(const vector[Sort] & es, const vector[Sort] & reps) except +
        size_t getDatatypeConstructorArity() except +
        vector[Sort] getDatatypeConstructorDomainSorts() except +
        Sort getDatatypeConstructorCodomainSort() except +
        Sort getDatatypeSelectorDomainSort() except +
        Sort getDatatypeSelectorCodomainSort() except +
        Sort getDatatypeTesterDomainSort() except +
        Sort getDatatypeTesterCodomainSort() except +
        size_t getFunctionArity() except +
        vector[Sort] getFunctionDomainSorts() except +
        Sort getFunctionCodomainSort() except +
        Sort getArrayIndexSort() except +
        Sort getArrayElementSort() except +
        Sort getSetElementSort() except +
        Sort getBagElementSort() except +
        SortKind getAbstractedKind() except +
        Sort getSequenceElementSort() except +
        size_t getUninterpretedSortConstructorArity() except +
        uint32_t getBitVectorSize() except +
        string getFiniteFieldSize() except +
        uint32_t getFloatingPointExponentSize() except +
        uint32_t getFloatingPointSignificandSize() except +
        size_t getDatatypeArity() except +
        size_t getTupleLength() except +
        vector[Sort] getTupleSorts() except +
        string toString() except +

    cdef cppclass SortHashFunction:
        SortHashFunction() except +
        size_t operator()(const Sort & s) except +

    cdef cppclass Stat:
        bint isInternal() except +
        bint isDefault() except +
        bint isInt() except +
        int64_t getInt() except +
        bint isDouble() except +
        double getDouble() except +
        bint isString() except +
        string getString() except +
        bint isHistogram() except +
        c_map[string,uint64_t] getHistogram() except +

    cdef cppclass Statistics:
        Statistics() except +
        cppclass iterator:
            iterator() except +
            bint operator!=(const iterator& it) except +
            iterator& operator++() except +
            pair[string, Stat]& operator*() except +;
        iterator begin(bint internal, bint defaulted) except +
        iterator end() except +
        Stat get(string name) except +

    cdef cppclass Term:
        Term()
        bint operator==(const Term&) except +
        bint operator!=(const Term&) except +
        bint operator<(const Term&) except +
        bint operator>(const Term&) except +
        bint operator<=(const Term&) except +
        bint operator>=(const Term&) except +
        size_t getNumChildren() except +
        Term operator[](size_t idx) except +
        uint64_t getId() except +
        Kind getKind() except +
        Sort getSort() except +
        Term substitute(const Term & es, const Term & reps) except +
        Term substitute(const vector[Term] & es, const vector[Term] & reps) except +
        bint hasOp() except +
        Op getOp() except +
        bint hasSymbol() except +
        string getSymbol() except +
        bint isNull() except +
        Term getConstArrayBase() except +
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
        bint isCardinalityConstraint() except +
        pair[Sort, uint32_t] getCardinalityConstraint() except +
        bint isRealAlgebraicNumber() except +
        Term getRealAlgebraicNumberDefiningPolynomial(const Term& v) except +
        Term getRealAlgebraicNumberLowerBound() except +
        Term getRealAlgebraicNumberUpperBound() except +

        bint isConstArray() except +
        bint isBooleanValue() except +
        bint getBooleanValue() except +
        bint isStringValue() except +
        wstring getStringValue() except +
        int32_t getRealOrIntegerValueSign() except +
        bint isIntegerValue() except +
        string getIntegerValue() except +
        bint isRealValue() except +
        string getRealValue() except +
        bint isBitVectorValue() except +
        string getBitVectorValue(uint32_t base) except +
        bint isFiniteFieldValue() except +
        string getFiniteFieldValue() except +
        bint isUninterpretedSortValue() except +
        string getUninterpretedSortValue() except +
        bint isTupleValue() except +
        vector[Term] getTupleValue() except +
        bint isRoundingModeValue() except +
        RoundingMode getRoundingModeValue() except +

        bint isFloatingPointPosZero() except +
        bint isFloatingPointNegZero() except +
        bint isFloatingPointPosInf() except +
        bint isFloatingPointNegInf() except +
        bint isFloatingPointNaN() except +
        bint isFloatingPointValue() except +

        tuple[uint32_t, uint32_t, Term] getFloatingPointValue() except +
        bint isSetValue() except +
        set[Term] getSetValue() except +
        bint isSequenceValue() except +
        vector[Term] getSequenceValue() except +


    cdef cppclass TermHashFunction:
        TermHashFunction() except +
        size_t operator()(const Term & t) except +
