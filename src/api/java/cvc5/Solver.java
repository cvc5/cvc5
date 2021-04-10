package cvc5;

import java.io.IOException;

public class Solver implements IPointer
{
  private final long pointer;

  public long getPointer()
  {
    return pointer;
  }

  public Solver()
  {
    this.pointer = newSolver();
  }

  private native long newSolver();

  public void deletePointer()
  {
    deletePointer(pointer);
  }

  private static native void deletePointer(long pointer);

  static
  {
    Utils.loadLibraries();
  }

  /* .................................................................... */
  /* Constructors/Destructors                                             */
  /* .................................................................... */

  /**
   * Constructor.
   * @param opts an optional pointer to a solver options object
   * @return the Solver
   */
  Solver(Options* opts = nullptr);

  /**
   * Destructor.
   */
  ~Solver();

  /**
   * Disallow copy/assignment.
   */
  Solver(Solver&) = delete;
  Solver& operator = (Solver&) = delete;

  /* .................................................................... */
  /* Solver Configuration                                                 */
  /* .................................................................... */

  public boolean supportsFloatingPoint()

      /* .................................................................... */
      /* Sorts Handling                                                       */
      /* .................................................................... */

      /**
       * @return sort null
       */
      Sort getNullSort()

      /**
       * @return sort Boolean
       */
      Sort getBooleanSort()

      /**
       * @return sort Integer (in CVC4, Integer is a subtype of Real)
       */
      Sort getIntegerSort()

      /**
       * @return sort Real
       */
      Sort getRealSort()

      /**
       * @return sort RegExp
       */
      Sort getRegExpSort()

      /**
       * @return sort RoundingMode
       */
      Sort getRoundingModeSort()

      /**
       * @return sort String
       */
      Sort getStringSort()

      /**
       * Create an array sort.
       * @param indexSort the array index sort
       * @param elemSort the array element sort
       * @return the array sort
       */
      Sort mkArraySort(Sort indexSort, Sort elemSort)

      /**
       * Create a bit-vector sort.
       * @param size the bit-width of the bit-vector sort
       * @return the bit-vector sort
       */
      Sort mkBitVectorSort(uint32_t size)

      /**
       * Create a floating-point sort.
       * @param exp the bit-width of the exponent of the floating-point sort.
       * @param sig the bit-width of the significand of the floating-point sort.
       */
      Sort mkFloatingPointSort(uint32_t exp, uint32_t sig)

      /**
       * Create a datatype sort.
       * @param dtypedecl the datatype declaration from which the sort is
       *     created
       * @return the datatype sort
       */
      Sort mkDatatypeSort(DatatypeDecl& dtypedecl)

      /**
       * Create a vector of datatype sorts. The names of the datatype
       * declarations must be distinct.
       *
       * @param dtypedecls the datatype declarations from which the sort is
       *     created
       * @return the datatype sorts
       */
      std::vector<Sort> mkDatatypeSorts(const std::vector<DatatypeDecl>& dtypedecls)

      /**
       * Create a vector of datatype sorts using unresolved sorts. The names of
       * the datatype declarations in dtypedecls must be distinct.
       *
       * This method is called when the DatatypeDecl objects dtypedecls have
       * been built using "unresolved" sorts.
       *
       * We associate each sort in unresolvedSorts with exacly one datatype from
       * dtypedecls. In particular, it must have the same name as exactly one
       * datatype declaration in dtypedecls.
       *
       * When constructing datatypes, unresolved sorts are replaced by the
       * datatype sort constructed for the datatype declaration it is associated
       * with.
       *
       * @param dtypedecls the datatype declarations from which the sort is
       *     created
       * @param unresolvedSorts the list of unresolved sorts
       * @return the datatype sorts
       */
      std::vector<Sort> mkDatatypeSorts(
          const std::vector<DatatypeDecl>& dtypedecls, const std::set<Sort>& unresolvedSorts)

      /**
       * Create function sort.
       * @param domain the sort of the fuction argument
       * @param codomain the sort of the function return value
       * @return the function sort
       */
      Sort mkFunctionSort(Sort domain, Sort codomain)

      /**
       * Create function sort.
       * @param sorts the sort of the function arguments
       * @param codomain the sort of the function return value
       * @return the function sort
       */
      Sort mkFunctionSort(std::vector<Sort>& sorts, Sort codomain)

      /**
       * Create a sort parameter.
       * @param symbol the name of the sort
       * @return the sort parameter
       */
      Sort mkParamSort(String symbol)

      /**
       * Create a predicate sort.
       * @param sorts the list of sorts of the predicate
       * @return the predicate sort
       */
      Sort mkPredicateSort(std::vector<Sort>& sorts)

      /**
       * Create a record sort
       * @param fields the list of fields of the record
       * @return the record sort
       */
      Sort mkRecordSort(const std::vector<std::pair<std::string, Sort>>& fields)

      /**
       * Create a set sort.
       * @param elemSort the sort of the set elements
       * @return the set sort
       */
      Sort mkSetSort(Sort elemSort)

      /**
       * Create a bag sort.
       * @param elemSort the sort of the bag elements
       * @return the bag sort
       */
      Sort mkBagSort(Sort elemSort)

      /**
       * Create a sequence sort.
       * @param elemSort the sort of the sequence elements
       * @return the sequence sort
       */
      Sort mkSequenceSort(Sort elemSort)

      /**
       * Create an uninterpreted sort.
       * @param symbol the name of the sort
       * @return the uninterpreted sort
       */
      Sort mkUninterpretedSort(String symbol)

      /**
       * Create a sort constructor sort.
       * @param symbol the symbol of the sort
       * @param arity the arity of the sort
       * @return the sort constructor sort
       */
      Sort mkSortConstructorSort(String symbol, size_t arity)

      /**
       * Create a tuple sort.
       * @param sorts of the elements of the tuple
       * @return the tuple sort
       */
      Sort mkTupleSort(std::vector<Sort>& sorts)

      /* .................................................................... */
      /* Create Terms                                                         */
      /* .................................................................... */

      /**
       * Create 0-ary term of given kind.
       * @param kind the kind of the term
       * @return the Term
       */
      Term mkTerm(Kind kind)

      /**
       * Create a unary term of given kind.
       * @param kind the kind of the term
       * @param child the child of the term
       * @return the Term
       */
      Term mkTerm(Kind kind, Term child)

      /**
       * Create binary term of given kind.
       * @param kind the kind of the term
       * @param child1 the first child of the term
       * @param child2 the second child of the term
       * @return the Term
       */
      Term mkTerm(Kind kind, Term child1, Term child2)

      /**
       * Create ternary term of given kind.
       * @param kind the kind of the term
       * @param child1 the first child of the term
       * @param child2 the second child of the term
       * @param child3 the third child of the term
       * @return the Term
       */
      Term mkTerm(Kind kind, Term child1, Term child2, Term child3)

      /**
       * Create n-ary term of given kind.
       * @param kind the kind of the term
       * @param children the children of the term
       * @return the Term
       */
      Term mkTerm(Kind kind, Term[] children)

      /**
       * Create nullary term of given kind from a given operator.
       * Create operators with mkOp().
       * @param op the operator
       * @return the Term
       */
      Term mkTerm(Op& op)

      /**
       * Create unary term of given kind from a given operator.
       * Create operators with mkOp().
       * @param op the operator
       * @param child the child of the term
       * @return the Term
       */
      Term mkTerm(Op& op, Term child)

      /**
       * Create binary term of given kind from a given operator.
       * Create operators with mkOp().
       * @param op the operator
       * @param child1 the first child of the term
       * @param child2 the second child of the term
       * @return the Term
       */
      Term mkTerm(Op& op, Term child1, Term child2)

      /**
       * Create ternary term of given kind from a given operator.
       * Create operators with mkOp().
       * @param op the operator
       * @param child1 the first child of the term
       * @param child2 the second child of the term
       * @param child3 the third child of the term
       * @return the Term
       */
      Term mkTerm(Op& op, Term child1, Term child2, Term child3)

      /**
       * Create n-ary term of given kind from a given operator.
       * Create operators with mkOp().
       * @param op the operator
       * @param children the children of the term
       * @return the Term
       */
      Term mkTerm(Op& op, Term[] children)

      /**
       * Create a tuple term. Terms are automatically converted if sorts are
       * compatible.
       * @param sorts The sorts of the elements in the tuple
       * @param terms The elements in the tuple
       * @return the tuple Term
       */
      Term mkTuple(std::vector<Sort>& sorts, Term[] terms)

      /* .................................................................... */
      /* Create Operators                                                     */
      /* .................................................................... */

      /**
       * Create an operator for a builtin Kind
       * The Kind may not be the Kind for an indexed operator
       *   (e.g. BITVECTOR_EXTRACT)
       * Note: in this case, the Op simply wraps the Kind.
       * The Kind can be used in mkTerm directly without
       *   creating an op first.
       * @param kind the kind to wrap
       */
      Op mkOp(Kind kind)

      /**
       * Create operator of kind:
       *   - RECORD_UPDATE
       *   - DIVISIBLE (to support arbitrary precision integers)
       * See enum Kind for a description of the parameters.
       * @param kind the kind of the operator
       * @param arg the string argument to this operator
       */
      Op mkOp(Kind kind, String arg)

      /**
       * Create operator of kind:
       *   - DIVISIBLE
       *   - BITVECTOR_REPEAT
       *   - BITVECTOR_ZERO_EXTEND
       *   - BITVECTOR_SIGN_EXTEND
       *   - BITVECTOR_ROTATE_LEFT
       *   - BITVECTOR_ROTATE_RIGHT
       *   - INT_TO_BITVECTOR
       *   - FLOATINGPOINT_TO_UBV
       *   - FLOATINGPOINT_TO_UBV_TOTAL
       *   - FLOATINGPOINT_TO_SBV
       *   - FLOATINGPOINT_TO_SBV_TOTAL
       *   - TUPLE_UPDATE
       * See enum Kind for a description of the parameters.
       * @param kind the kind of the operator
       * @param arg the uint32_t argument to this operator
       */
      Op mkOp(Kind kind, uint32_t arg)

      /**
       * Create operator of Kind:
       *   - BITVECTOR_EXTRACT
       *   - FLOATINGPOINT_TO_FP_IEEE_BITVECTOR
       *   - FLOATINGPOINT_TO_FP_FLOATINGPOINT
       *   - FLOATINGPOINT_TO_FP_REAL
       *   - FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR
       *   - FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR
       *   - FLOATINGPOINT_TO_FP_GENERIC
       * See enum Kind for a description of the parameters.
       * @param kind the kind of the operator
       * @param arg1 the first uint32_t argument to this operator
       * @param arg2 the second uint32_t argument to this operator
       */
      Op mkOp(Kind kind, uint32_t arg1, uint32_t arg2)

      /**
       * Create operator of Kind:
       *   - TUPLE_PROJECT
       * See enum Kind for a description of the parameters.
       * @param kind the kind of the operator
       * @param args the arguments (indices) of the operator
       */
      Op mkOp(Kind kind, const std::vector<uint32_t>& args)

      /* .................................................................... */
      /* Create Constants                                                     */
      /* .................................................................... */

      /**
       * Create a Boolean true constant.
       * @return the true constant
       */
      Term mkTrue()

      /**
       * Create a Boolean false constant.
       * @return the false constant
       */
      Term mkFalse()

      /**
       * Create a Boolean constant.
       * @return the Boolean constant
       * @param val the value of the constant
       */
      Term mkBoolean(bool val)

      /**
       * Create a constant representing the number Pi.
       * @return a constant representing Pi
       */
      Term mkPi()
      /**
       * Create an integer constant from a string.
       * @param s the string representation of the constant, may represent an
       *          integer (e.g., "123").
       * @return a constant of sort Integer assuming 's' represents an integer)
       */
      Term mkInteger(String s)

      /**
       * Create an integer constant from a c++ int.
       * @param val the value of the constant
       * @return a constant of sort Integer
       */
      Term mkInteger(int64_t val)

      /**
       * Create a real constant from a string.
       * @param s the string representation of the constant, may represent an
       *          integer (e.g., "123") or real constant (e.g., "12.34" or
       * "12/34").
       * @return a constant of sort Real
       */
      Term mkReal(String s)

      /**
       * Create a real constant from an integer.
       * @param val the value of the constant
       * @return a constant of sort Integer
       */
      Term mkReal(int64_t val)

      /**
       * Create a real constant from a rational.
       * @param num the value of the numerator
       * @param den the value of the denominator
       * @return a constant of sort Real
       */
      Term mkReal(int64_t num, int64_t den)

      /**
       * Create a regular expression empty term.
       * @return the empty term
       */
      Term mkRegexpEmpty()

      /**
       * Create a regular expression sigma term.
       * @return the sigma term
       */
      Term mkRegexpSigma()

      /**
       * Create a constant representing an empty set of the given sort.
       * @param sort the sort of the set elements.
       * @return the empty set constant
       */
      Term mkEmptySet(Sort sort)

      /**
       * Create a constant representing an empty bag of the given sort.
       * @param sort the sort of the bag elements.
       * @return the empty bag constant
       */
      Term mkEmptyBag(Sort sort)

      /**
       * Create a separation logic nil term.
       * @param sort the sort of the nil term
       * @return the separation logic nil term
       */
      Term mkSepNil(Sort sort)

      /**
       * Create a String constant.
       * @param s the string this constant represents
       * @param useEscSequences determines whether escape sequences in \p s
       *     should
       * be converted to the corresponding character
       * @return the String constant
       */
      Term mkString(String s, bool useEscSequences = false)

      /**
       * Create a String constant.
       * @param c the character this constant represents
       * @return the String constant
       */
      Term mkString(unsigned char c)

      /**
       * Create a String constant.
       * @param s a list of unsigned (unicode) values this constant represents
       *     as
       * string
       * @return the String constant
       */
      Term mkString(std::vector<uint32_t>& s)

      /**
       * Create a character constant from a given string.
       * @param s the string denoting the code point of the character (in base
       *     16)
       * @return the character constant
       */
      Term mkChar(String s)

      /**
       * Create an empty sequence of the given element sort.
       * @param sort The element sort of the sequence.
       * @return the empty sequence with given element sort.
       */
      Term mkEmptySequence(Sort sort)

      /**
       * Create a universe set of the given sort.
       * @param sort the sort of the set elements
       * @return the universe set constant
       */
      Term mkUniverseSet(Sort sort)

      /**
       * Create a bit-vector constant of given size and value.
       * @param size the bit-width of the bit-vector sort
       * @param val the value of the constant
       * @return the bit-vector constant
       */
      Term mkBitVector(uint32_t size, uint64_t val = 0)

      /**
       * Create a bit-vector constant from a given string of base 2, 10 or 16.
       *
       * The size of resulting bit-vector is
       * - base  2: the size of the binary string
       * - base 10: the min. size required to represent the decimal as a
       * bit-vector
       * - base 16: the max. size required to represent the hexadecimal as a
       *            bit-vector (4 * size of the given value string)
       *
       * @param s the string representation of the constant
       * @param base the base of the string representation (2, 10, or 16)
       * @return the bit-vector constant
       */
      Term mkBitVector(String s, uint32_t base = 2)

      /**
       * Create a bit-vector constant of a given bit-width from a given string
       * of base 2, 10 or 16.
       * @param size the bit-width of the constant
       * @param s the string representation of the constant
       * @param base the base of the string representation (2, 10, or 16)
       * @return the bit-vector constant
       */
      Term mkBitVector(uint32_t size, String s, uint32_t base)

      /**
       * Create a constant array with the provided constant value stored at
       * every index
       * @param sort the sort of the constant array (must be an array sort)
       * @param val the constant value to store (must match the sort's element
       *     sort)
       * @return the constant array term
       */
      Term mkConstArray(Sort sort, Term val)

      /**
       * Create a positive infinity floating-point constant. Requires CVC4 to be
       * compiled with SymFPU support.
       * @param exp Number of bits in the exponent
       * @param sig Number of bits in the significand
       * @return the floating-point constant
       */
      Term mkPosInf(uint32_t exp, uint32_t sig)

      /**
       * Create a negative infinity floating-point constant. Requires CVC4 to be
       * compiled with SymFPU support.
       * @param exp Number of bits in the exponent
       * @param sig Number of bits in the significand
       * @return the floating-point constant
       */
      Term mkNegInf(uint32_t exp, uint32_t sig)

      /**
       * Create a not-a-number (NaN) floating-point constant. Requires CVC4 to
       * be compiled with SymFPU support.
       * @param exp Number of bits in the exponent
       * @param sig Number of bits in the significand
       * @return the floating-point constant
       */
      Term mkNaN(uint32_t exp, uint32_t sig)

      /**
       * Create a positive zero (+0.0) floating-point constant. Requires CVC4 to
       * be compiled with SymFPU support.
       * @param exp Number of bits in the exponent
       * @param sig Number of bits in the significand
       * @return the floating-point constant
       */
      Term mkPosZero(uint32_t exp, uint32_t sig)

      /**
       * Create a negative zero (-0.0) floating-point constant. Requires CVC4 to
       * be compiled with SymFPU support.
       * @param exp Number of bits in the exponent
       * @param sig Number of bits in the significand
       * @return the floating-point constant
       */
      Term mkNegZero(uint32_t exp, uint32_t sig)

      /**
       * Create a roundingmode constant.
       * @param rm the floating point rounding mode this constant represents
       */
      Term mkRoundingMode(RoundingMode rm)

      /**
       * Create uninterpreted constant.
       * @param sort Sort of the constant
       * @param index Index of the constant
       */
      Term mkUninterpretedConst(Sort sort, int32_t index)

      /**
       * Create an abstract value constant.
       * @param index Index of the abstract value
       */
      Term mkAbstractValue(String index)

      /**
       * Create an abstract value constant.
       * @param index Index of the abstract value
       */
      Term mkAbstractValue(uint64_t index)

      /**
       * Create a floating-point constant (requires CVC4 to be compiled with
       * symFPU support).
       * @param exp Size of the exponent
       * @param sig Size of the significand
       * @param val Value of the floating-point constant as a bit-vector term
       */
      Term mkFloatingPoint(uint32_t exp, uint32_t sig, Term val)

      /* .................................................................... */
      /* Create Variables                                                     */
      /* .................................................................... */

      /**
       * Create (first-order) constant (0-arity function symbol).
       * SMT-LIB:
       * \verbatim
       *   ( declare-const <symbol> <sort> )
       *   ( declare-fun <symbol> ( ) <sort> )
       * \endverbatim
       *
       * @param sort the sort of the constant
       * @param symbol the name of the constant
       * @return the first-order constant
       */
      Term mkConst(Sort sort, String symbol)
      /**
       * Create (first-order) constant (0-arity function symbol), with a default
       * symbol name.
       *
       * @param sort the sort of the constant
       * @return the first-order constant
       */
      Term mkConst(Sort sort)

      /**
       * Create a bound variable to be used in a binder (i.e. a quantifier, a
       * lambda, or a witness binder).
       * @param sort the sort of the variable
       * @param symbol the name of the variable
       * @return the variable
       */
      Term mkVar(Sort sort, String symbol = std::string())

      /* .................................................................... */
      /* Create datatype constructor declarations                             */
      /* .................................................................... */

      DatatypeConstructorDecl mkDatatypeConstructorDecl(String name);

  /* .................................................................... */
  /* Create datatype declarations                                         */
  /* .................................................................... */

  /**
   * Create a datatype declaration.
   * @param name the name of the datatype
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl mkDatatypeDecl(String name, public boolean isCoDatatype = false);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param param the sort parameter
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl mkDatatypeDecl(String name, Sort param, public boolean isCoDatatype = false);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl mkDatatypeDecl(
      String name, const std::vector<Sort>& params, public boolean isCoDatatype = false);

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   * @param t the formula to simplify
   * @return the simplified formula
   */
  public Term simplify(Term t)
  {
    long termPointer = simplify(pointer, t.getPointer());
    return new Term(solver, termPointer);
  }

  private native long simplify(long pointer, long termPointer);

  /**
   * Assert a formula.
   * SMT-LIB:
   * \verbatim
   *   ( assert <term> )
   * \endverbatim
   * @param term the formula to assert
   */
  public void assertFormula(Term term)
  {
    assertFormula(pointer, term.getPointer());
  }

  private native void assertFormula(long pointer, long termPointer);

  /**
   * Check satisfiability.
   * SMT-LIB:
   * \verbatim
   *   ( check-sat )
   * \endverbatim
   * @return the result of the satisfiability check.
   */
  public Result checkSat()
  {
    long resultPointer = checkSat(pointer);
    return new Result(solver, resultPointer);
  }

  private native long checkSat(long pointer);
  /**
   * Check satisfiability assuming the given formula.
   * SMT-LIB:
   * \verbatim
   *   ( check-sat-assuming ( <prop_literal> ) )
   * \endverbatim
   * @param assumption the formula to assume
   * @return the result of the satisfiability check.
   */
  Result checkSatAssuming(Term assumption)
  {
    long resultPointer = checkSatAssuming(pointer, assumption.getPointer());
    return new Result(solver, resultPointer);
  }

  private native long checkSatAssuming(long pointer, long assumptionPointer);

  /**
   * Check satisfiability assuming the given formulas.
   * SMT-LIB:
   * \verbatim
   *   ( check-sat-assuming ( <prop_literal>+ ) )
   * \endverbatim
   * @param assumptions the formulas to assume
   * @return the result of the satisfiability check.
   */
  public Result checkSatAssuming(Term[] assumptions)
  {
    long[] pointers = Utils.getPointers(assumptions);
    long resultPointer = checkSatAssuming(pointer, pointers);
    return new Result(solver, resultPointer);
  }

  private native long checkSatAssuming(long pointer, long[] assumptionPointers);

  /**
   * Check entailment of the given formula w.r.t. the current set of assertions.
   * @param term the formula to check entailment for
   * @return the result of the entailment check.
   */
  public Result checkEntailed(Term term)
  {
    long resultPointer = checkEntailed(pointer, term.getPointer());
    return new Result(solver, resultPointer);
  }

  private native long checkEntailed(long pointer, long termPointer);

  /**
   * Check entailment of the given set of given formulas w.r.t. the current
   * set of assertions.
   * @param terms the terms to check entailment for
   * @return the result of the entailmentcheck.
   */
  public Result checkEntailed(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    long resultPointer = checkEntailed(pointer, pointers);
    return new Result(solver, resultPointer);
  }

  private native long checkEntailed(long pointer, long[] termPointers);

  /**
   * Create datatype sort.
   * SMT-LIB:
   * \verbatim
   *   ( declare-datatype <symbol> <datatype_decl> )
   * \endverbatim
   * @param symbol the name of the datatype sort
   * @param ctors the constructor declarations of the datatype sort
   * @return the datatype sort
   */
  public Sort declareDatatype(String symbol, DatatypeConstructorDecl[] ctors)
  {
    long[] pointers = Utils.getPointers(ctors);
    long sortPointer = declareDatatype(pointer, symbol, pointers);
    return new Sort(solver, sortPointer);
  }

  private native long declareDatatype(long pointer, String symbol, long[] declPointers);

  /**
   * Declare n-ary function symbol.
   * SMT-LIB:
   * \verbatim
   *   ( declare-fun <symbol> ( <sort>* ) <sort> )
   * \endverbatim
   * @param symbol the name of the function
   * @param sorts the sorts of the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  public Term declareFun(String symbol, Sort[] sorts, Sort sort)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareFun(pointer, symbol, sortPointers, sort.getPointer);
    return new Term(solver, termPointer);
  }

  private native long declareFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer);

  /**
   * Declare uninterpreted sort.
   * SMT-LIB:
   * \verbatim
   *   ( declare-sort <symbol> <numeral> )
   * \endverbatim
   * @param symbol the name of the sort
   * @param arity the arity of the sort
   * @return the sort
   */
  public Sort declareSort(String symbol, int arity)
  {
    validateUnsigned(arity, "arity");
    long sortPointer = declareSort(pointer, symbol, arity);
    return new Sort(solver, sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity);

  /**
   * Define n-ary function in the current context.
   * SMT-LIB:
   * \verbatim
   *   ( define-fun <function_def> )
   * \endverbatim
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @return the function
   */
  public Term defineFun(String symbol, Term[] bound_vars, Sort sort, Term term)
  {
    return defineFun(symbol, bound_vars, sort, term);
  }

  /**
   * Define n-ary function.
   * SMT-LIB:
   * \verbatim
   *   ( define-fun <function_def> )
   * \endverbatim
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFun(String symbol, Term[] bound_vars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(bound_vars);
    long termPointer =
        defineFun(pointer, symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(solver, termPointer);
  }

  private native long defineFun(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define n-ary function in the current context.
   * SMT-LIB:
   * \verbatim
   * ( define-fun <function_def> )
   * \endverbatim
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @return the function
   */
  public Term defineFun(Term fun, Term[] bound_vars, Term term)
  {
    return defineFun(fun, bound_vars, term, false);
  }
  /**
   * Define n-ary function.
   * SMT-LIB:
   * \verbatim
   * ( define-fun <function_def> )
   * \endverbatim
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFun(Term fun, Term[] bound_vars, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(bound_vars);
    long termPointer = defineFun(pointer, boundVarPointers, term.getPointer(), global);
    return new Term(solver, termPointer);
  }

  private native long defineFun(
      long pointer, long[] boundVarPointers, long termPointer, boolean global);

  /**
   * Define recursive function in the current context.
   * SMT-LIB:
   * \verbatim
   * ( define-fun-rec <function_def> )
   * \endverbatim
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @return the function
   */
  public Term defineFunRec(String symbol, Term[] bound_vars, Sort sort, Term term)
  {
    defineFunsRec(symbol, bound_vars, sort, term, false);
  }

  /**
   * Define recursive function.
   * SMT-LIB:
   * \verbatim
   * ( define-fun-rec <function_def> )
   * \endverbatim
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFunRec(String symbol, Term[] bound_vars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(bound_vars);
    defineFunRec(pointer, symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
  }

  private native void defineFunRec(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   * SMT-LIB:
   * \verbatim
   * ( define-fun-rec <function_def> )
   * \endverbatim
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @return the function
   */

  public Term defineFunRec(Term fun, Term[] bound_vars, Term term, boolean global)
  {
    defineFunRec(fun, bound_vars, term, false);
  }

  /**
   * Define recursive function.
   * SMT-LIB:
   * \verbatim
   * ( define-fun-rec <function_def> )
   * \endverbatim
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFunRec(Term fun, Term[] bound_vars, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(bound_vars);
    defineFunRec(pointer, fun.getPointer(), boundVarPointers, term.getPointer(), global);
  }

  private native void defineFunRec(
      long pointer, long funPointer, long[] boundVarPointers, long termPointer, boolean global);

  /**
   * Define recursive functions in the current context.
   * SMT-LIB:
   * \verbatim
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * \endverbatim
   * Create elements of parameter 'funs' with mkConst().
   * @param funs the sorted functions
   * @param bound_vars the list of parameters to the functions
   * @param terms the list of function bodies of the functions
   * @return the function
   */
  public void defineFunsRec(Term[] funs, Term[][] bound_vars, Term[] terms)
  {
    defineFunsRec(funs, bound_vars, terms, false);
  }
  /**
   * Define recursive functions.
   * SMT-LIB:
   * \verbatim
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * \endverbatim
   * Create elements of parameter 'funs' with mkConst().
   * @param funs the sorted functions
   * @param bound_vars the list of parameters to the functions
   * @param terms the list of function bodies of the functions
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public void defineFunsRec(Term[] funs, Term[][] bound_vars, Term[] terms, boolean)
  {
    long[] funPointers = Utils.getPointers(funs);
    long[][] boundVarPointers = Utils.getPointers(bound_vars);
    long[] termPointers = Utils.getPointers(terms);
    defineFunsRec(pointer, funPointers, boundVarPointers, termPointers, global);
  }

  private native void defineFunsRec(long pointer,
      long[] funPointers,
      long[][] boundVarPointers,
      long[] termPointers,
      boolean global);

  /**
   * Echo a given string to the given output stream.
   * SMT-LIB:
   * \verbatim
   * ( echo <std::string> )
   * \endverbatim
   * @param out the output stream
   * @param str the string to echo
   */
  // TODO: void echo(std::ostream& out, String  str)

  /**
   * Get the list of asserted formulas.
   * SMT-LIB:
   * \verbatim
   * ( get-assertions )
   * \endverbatim
   * @return the list of asserted formulas
   */
  public Term[] getAssertions()
  {
    long retPointers = getAssertions(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getAssertions(long pointer);

  /**
   * Get info from the solver.
   * SMT-LIB: \verbatim( get-info <info_flag> )\verbatim
   * @return the info
   */
  public String getInfo(String flag)
  {
    return getInfo(pointer, flag);
  }

  private native String getInfo(long pointer, String flag);

  /**
   * Get the value of a given option.
   * SMT-LIB:
   * \verbatim
   * ( get-option <keyword> )
   * \endverbatim
   * @param option the option for which the value is queried
   * @return a string representation of the option value
   */
  public String getOption(String option)
  {
    return getOption(pointer, option);
  }

  private native String getOption(long pointer, String option);

  /**
   * Get the set of unsat ("failed") assumptions.
   * SMT-LIB:
   * \verbatim
   * ( get-unsat-assumptions )
   * \endverbatim
   * Requires to enable option 'produce-unsat-assumptions'.
   * @return the set of unsat assumptions.
   */
  public Term[] getUnsatAssumptions()
  {
    long retPointers = getUnsatAssumptions(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getUnsatAssumptions(long pointer);

  /**
   * Get the unsatisfiable core.
   * SMT-LIB:
   * \verbatim
   * ( get-unsat-core )
   * \endverbatim
   * Requires to enable option 'produce-unsat-cores'.
   * @return a set of terms representing the unsatisfiable core
   */
  public Term[] getUnsatCore()
  {
    long retPointers = getUnsatCore(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getUnsatCore(long pointer);

  /**
   * Get the value of the given term.
   * SMT-LIB:
   * \verbatim
   * ( get-value ( <term> ) )
   * \endverbatim
   * @param term the term for which the value is queried
   * @return the value of the given term
   */
  public Term getValue(Term term)
  {
    long termPointer = getValue(pointer, term.getPointer());
    return new Term(solver, termPointer);
  }

  private native long getValue(long pointer, long termPointer);

  /**
   * Get the values of the given terms.
   * SMT-LIB:
   * \verbatim
   * ( get-value ( <term>+ ) )
   * \endverbatim
   * @param terms the terms for which the value is queried
   * @return the values of the given terms
   */
  public Term[] getValue(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    long[] retPointers = getValue(pointer, pointers);
    return Utils.getTerms(solver, retPointers);
  }

  private native long[] getValue(long pointer, long[] termPointers);

  /**
   * Do quantifier elimination.
   * SMT-LIB:
   * \verbatim
   * ( get-qe <q> )
   * \endverbatim
   * Requires a logic that supports quantifier elimination. Currently, the only
   * logics supported by quantifier elimination is LRA and LIA.
   * @param q a quantified formula of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free formula
   * @return a formula ret such that, given the current set of formulas A
   * asserted to this solver:
   *   - ( A ^ q ) and ( A ^ ret ) are equivalent
   *   - ret is quantifier-free formula containing only free variables in
   *     y1...yn.
   */
  public Term getQuantifierElimination(Term q)
  {
    long termPointer = getQuantifierElimination(q.getPointer());
  }

  private native long getQuantifierElimination(long pointer, long qPointer);

  /**
   * Do partial quantifier elimination, which can be used for incrementally
   * computing the result of a quantifier elimination.
   * SMT-LIB:
   * \verbatim
   * ( get-qe-disjunct <q> )
   * \endverbatim
   * Requires a logic that supports quantifier elimination. Currently, the only
   * logics supported by quantifier elimination is LRA and LIA.
   * @param q a quantified formula of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free formula
   * @return a formula ret such that, given the current set of formulas A
   * asserted to this solver:
   *   - (A ^ q) => (A ^ ret) if Q is forall or (A ^ ret) => (A ^ q) if Q is
   *     exists,
   *   - ret is quantifier-free formula containing only free variables in
   *     y1...yn,
   *   - If Q is exists, let A^Q_n be the formula
   *       A ^ ~ret^Q_1 ^ ... ^ ~ret^Q_n
   *     where for each i=1,...n, formula ret^Q_i is the result of calling
   *     getQuantifierEliminationDisjunct for q with the set of assertions
   *     A^Q_{i-1}. Similarly, if Q is forall, then let A^Q_n be
   *       A ^ ret^Q_1 ^ ... ^ ret^Q_n
   *     where ret^Q_i is the same as above. In either case, we have
   *     that ret^Q_j will eventually be true or false, for some finite j.
   */
  public Term getQuantifierEliminationDisjunct(Term q)
  {
    long termPointer = getQuantifierEliminationDisjunct(pointer, qPointer);
    return new Pointer(solver, termPointer);
  }

  private native long getQuantifierEliminationDisjunct(long pointer, long qPointer);

  /**
   * When using separation logic, this sets the location sort and the
   * datatype sort to the given ones. This method should be invoked exactly
   * once, before any separation logic constraints are provided.
   * @param locSort The location sort of the heap
   * @param dataSort The data sort of the heap
   */
  public void declareSeparationHeap(Sort locSort, Sort dataSort)
  {
    declareSeparationHeap(pointer, locSort.getPointer(), dataSort.getPointer());
  }

  private native void declareSeparationHeap(pointer, locSortPointer, dataSortPointer);

  /**
   * When using separation logic, obtain the term for the heap.
   * @return The term for the heap
   */
  public Term getSeparationHeap()
  {
    long termPointer = getSeparationHeap(pointer);
    return new Term(solver, termPointer);
  }

  private native long getSeparationHeap(long pointer);

  /**
   * When using separation logic, obtain the term for nil.
   * @return The term for nil
   */
  public Term getSeparationNilTerm()
      /**
       * Pop a level from the assertion stack.
       * SMT-LIB:
       * \verbatim
       * ( pop <numeral> )
       * \endverbatim
       */
      public void pop()
  {
    pop(1);
  }

  /**
   * Pop (a) level(s) from the assertion stack.
   * SMT-LIB:
   * \verbatim
   * ( pop <numeral> )
   * \endverbatim
   * @param nscopes the number of levels to pop
   */
  public void pop(uint32_t nscopes)
  {
    if (nscopes < 0)
    {
      throw new CVC5ApiException("Expected nscopes '" + nscopes + "' to be non negative.");
    }
    pop(pointer, nscopes);
  }

  private native void pop(long pointer, int nscopes);

  /**
   * Get an interpolant
   * SMT-LIB:
   * \verbatim
   * ( get-interpol <conj> )
   * \endverbatim
   * Requires to enable option 'produce-interpols'.
   * @param conj the conjecture term
   * @param output a Term I such that A->I and I->B are valid, where A is the
   *        current set of assertions and B is given in the input by conj.
   * @return true if it gets I successfully, false otherwise.
   */
  public boolean getInterpolant(Term conj, Term output)
  {
    return getInterpolant(pointer, conj.getPointer(), output.getPointer);
  }

  private native boolean getInterpolant(long pointer, long conjPointer, long outputPointer);

  /**
   * Get an interpolant
   * SMT-LIB:
   * \verbatim
   * ( get-interpol <conj> <g> )
   * \endverbatim
   * Requires to enable option 'produce-interpols'.
   * @param conj the conjecture term
   * @param grammar the grammar for the interpolant I
   * @param output a Term I such that A->I and I->B are valid, where A is the
   *        current set of assertions and B is given in the input by conj.
   * @return true if it gets I successfully, false otherwise.
   */
  public boolean getInterpolant(Term conj, Grammar grammar, Term output)
  {
    return getInterpolant(pointer, conj.getPointer(), grammar.getPointer(), output.getPointer);
  }

  private native boolean getInterpolant(
      long pointer, long conjPointer, long grammarPointer, long outputPointer);

  /**
   * Get an abduct.
   * SMT-LIB:
   * \verbatim
   * ( get-abduct <conj> )
   * \endverbatim
   * Requires enabling option 'produce-abducts'
   * @param conj the conjecture term
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj
   * @return true if it gets C successfully, false otherwise
   */
  public boolean getAbduct(Term conj, Term output)
  {
    return getAbduct(pointer, conj.getPointer(), output.getPointer);
  }

  private native boolean getAbduct(long pointer, long conjPointer, long outputPointer);
  /**
   * Get an abduct.
   * SMT-LIB:
   * \verbatim
   * ( get-abduct <conj> <g> )
   * \endverbatim
   * Requires enabling option 'produce-abducts'
   * @param conj the conjecture term
   * @param grammar the grammar for the abduct C
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj
   * @return true if it gets C successfully, false otherwise
   */
  public boolean getAbduct(Term conj, Grammar grammar, Term output)
  {
    return getAbduct(pointer, conj.getPointer(), grammar.getPointer(), output.getPointer);
  }

  private native boolean getAbduct(
      long pointer, long conjPointer, long grammarPointer, long outputPointer);

  /**
   * Block the current model. Can be called only if immediately preceded by a
   * SAT or INVALID query.
   * SMT-LIB:
   * \verbatim
   * ( block-model )
   * \endverbatim
   * Requires enabling 'produce-models' option and setting 'block-models' option
   * to a mode other than "none".
   */
  public void blockModel()
  {
    blockModel(pointer);
  }

  private native void blockModel(long pointer);

  /**
   * Block the current model values of (at least) the values in terms. Can be
   * called only if immediately preceded by a SAT or NOT_ENTAILED query.
   * SMT-LIB:
   * \verbatim
   * ( block-model-values ( <terms>+ ) )
   * \endverbatim
   * Requires enabling 'produce-models' option and setting 'block-models' option
   * to a mode other than "none".
   */
  public void blockModelValues(Term[] terms)
  {
    long pointers = Utils.getPointers(terms);
    blockModelValues(pointer, pointers);
  }

  private native void blockModelValues(long pointer, long[] termPointers);

  /**
   * Print all instantiations made by the quantifiers module.
   * @param out the output stream
   */
  // TODO: void printInstantiations(std::ostream& out)

  /**
   * Push a level to the assertion stack.
   * SMT-LIB:
   * \verbatim
   * ( push <numeral> )
   * \endverbatim
   */
  public void push(int nscopes = 1)
  {
    push(1);
  }

  /**
   * Push (a) level(s) to the assertion stack.
   * SMT-LIB:
   * \verbatim
   * ( push <numeral> )
   * \endverbatim
   * @param nscopes the number of levels to push
   */
  public void push(int nscopes)
  {
    if (nscopes < 0)
    {
      throw new CVC5ApiException("Expected nscopes '" + nscopes + "' to be non negative.");
    }
    push(pointer, nscopes);
  }

  private native void push(long pointer, int nscopes);

  /**
   * Remove all assertions.
   * SMT-LIB:
   * \verbatim
   * ( reset-assertions )
   * \endverbatim
   */
  public void resetAssertions()
  {
    resetAssertions(pointer);
  }

  private native void resetAssertions(long pointer);

  /**
   * Set info.
   * SMT-LIB:
   * \verbatim
   * ( set-info <attribute> )
   * \endverbatim
   * @param keyword the info flag
   * @param value the value of the info flag
   */
  public void setInfo(String keyword, String value) throws CVC5ApiException
  {
    setInfo(pointer, keyword, value);
  }

  private native void setInfo(long pointer, String keyword, String value) throws CVC5ApiException;

  /**
   * Set logic.
   * SMT-LIB:
   * \verbatim
   * ( set-logic <symbol> )
   * \endverbatim
   * @param logic the logic to set
   */
  public void setLogic(String logic) throws CVC5ApiException
  {
    setLogic(pointer, logic);
  }

  private native void setLogic(long pointer, String logic) throws CVC5ApiException;

  /**
   * Set option.
   * SMT-LIB:
   * \verbatim
   *   ( set-option <option> )
   * \endverbatim
   * @param option the option name
   * @param value the option value
   */
  public void setOption(String option, String value)
  {
    setOption(pointer, option, value);
  }

  private native void setOption(long pointer, String option, String value);

  /**
   * If needed, convert this term to a given sort. Note that the sort of the
   * term must be convertible into the target sort. Currently only Int to Real
   * conversions are supported.
   * @param t the term
   * @param s the target sort
   * @return the term wrapped into a sort conversion if needed
   */
  public Term ensureTermSort(Term t, Sort s)
  {
    long termPointer = ensureTermSort(pointer, t.getPointer(), s.getPointer());
    return new Term(solver, termPointer);
  }

  private native long ensureTermSort(long pointer, termPointer, sortPointer);

  /**
   * Append \p symbol to the current list of universal variables.
   * @param sort the sort of the universal variable
   * @return the universal variable
   */
  public Term mkSygusVar(Sort sort)
  {
    return mkSygusVar(sort, "");
  }
  /**
   * Append \p symbol to the current list of universal variables.
   * SyGuS v2:
   * \verbatim
   *   ( declare-var <symbol> <sort> )
   * \endverbatim
   * @param sort the sort of the universal variable
   * @param symbol the name of the universal variable
   * @return the universal variable
   */
  public Term mkSygusVar(Sort sort, String symbol)
  {
    long termPointer = mkSygusVar(pointer, sort.getPointer(), symbol);
    return new Term(solver, termPointer);
  }

  private native long mkSygusVar(long pointer, long sortPointer, String symbol);

  /**
   * Create a Sygus grammar. The first non-terminal is treated as the starting
   * non-terminal, so the order of non-terminals matters.
   *
   * @param boundVars the parameters to corresponding synth-fun/synth-inv
   * @param ntSymbols the pre-declaration of the non-terminal symbols
   * @return the grammar
   */
  public Grammar mkSygusGrammar(Term[] boundVars, Term[] ntSymbols)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long[] ntSymbolPointers = Utils.getPointers(ntSymbols);
    long termPointer = synthFun(pointer, symbol, boundVarPointers, ntSymbolPointers);
    return new Term(solver, termPointer);
  }

  private native long mkSygusGrammar(
      long pointer, long[] boundVarPointers, long[] ntSymbolPointers);

  /**
   * Synthesize n-ary function.
   * SyGuS v2:
   * \verbatim
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> )
   * \endverbatim
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthFun(pointer, symbol, boundVarPointers, sort.getPointer());
    return new Term(solver, termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer);

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   * SyGuS v2:
   * \verbatim
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )
   * \endverbatim
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param grammar the syntactic constraints
   * @return the function
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort, Grammar grammar)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        synthFun(pointer, symbol, boundVarPointers, sort.getPointer(), grammar.getPointer());
    return new Term(solver, termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer, long grammarPointer);

  /**
   * Synthesize invariant.
   * SyGuS v2:
   * \verbatim
   *   ( synth-inv <symbol> ( <boundVars>* ) )
   * \endverbatim
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @return the invariant
   */
  public Term synthInv(String symbol, Term[] boundVars)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthInv(pointer, symbol, boundVarPointers);
    return new Term(solver, termPointer);
  }

  private native long synthInv(long pointer, String symbol, long[] boundVarPointers);

  /**
   * Synthesize invariant following specified syntactic constraints.
   * SyGuS v2:
   * \verbatim
   *   ( synth-inv <symbol> ( <boundVars>* ) <g> )
   * \endverbatim
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @param grammar the syntactic constraints
   * @return the invariant
   */
  public Term synthInv(String symbol, Term[] boundVars, Grammar grammar)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthInv(pointer, symbol, boundVarPointers, grammar.getPointer());
    return new Term(solver, termPointer);
  }

  private native long synthInv(
      long pointer, String symbol, long[] boundVarPointers, long grammarPointer);

  /**
   * Add a forumla to the set of Sygus constraints.
   * SyGuS v2:
   * \verbatim
   *   ( constraint <term> )
   * \endverbatim
   * @param term the formula to add as a constraint
   */
  void addSygusConstraint(Term term)
  {
    addSygusConstraint(pointer, term.getPointer());
  }

  private native void addSygusConstraint(long pointer, long termPointer);
  /**
   * Add a set of Sygus constraints to the current state that correspond to an
   * invariant synthesis problem.
   * SyGuS v2:
   * \verbatim
   *   ( inv-constraint <inv> <pre> <trans> <post> )
   * \endverbatim
   * @param inv the function-to-synthesize
   * @param pre the pre-condition
   * @param trans the transition relation
   * @param post the post-condition
   */
  public void addSygusInvConstraint(Term inv, Term pre, Term trans, Term post)
  {
        addSygusConstraint(pointer, inv.getPointer(), pre.getPointer()), trans.getPointer(), post.getPointer());
  }

  private native void addSygusConstraint(
      long pointer, long invPointer, long prePointer, long transPointer, long postPointer);

  /**
   * Try to find a solution for the synthesis conjecture corresponding to the
   * current list of functions-to-synthesize, universal variables and
   * constraints.
   * SyGuS v2:
   * \verbatim
   *   ( check-synth )
   * \endverbatim
   * @return the result of the synthesis conjecture.
   */
  public Result checkSynth()
  {
    long resultPointer = checkSynth(pointer);
    return new Result(solver, resultPointer);
  }

  private native long checkSynth(long pointer);

  /**
   * Get the synthesis solution of the given term. This method should be called
   * immediately after the solver answers unsat for sygus input.
   * @param term the term for which the synthesis solution is queried
   * @return the synthesis solution of the given term
   */
  public Term getSynthSolution(Term term)
  {
    long termPointer = getSynthSolution(pointer, term.getPointer());
    return new Term(solver, termPointer);
  }

  private native long getSynthSolution(long pointer, long termPointer);

  /**
   * Get the synthesis solutions of the given terms. This method should be
   * called immediately after the solver answers unsat for sygus input.
   * @param terms the terms for which the synthesis solutions is queried
   * @return the synthesis solutions of the given terms
   */
  public Term[] getSynthSolutions(Term[] terms)
  {
    long[] termPointers = Utils.getPointers(terms);
    long[] retPointers = getSynthSolutions(pointer, termPointers);
    return Utils.getTerms(solver, retPointers);
  }

  private native long[] getSynthSolutions(long pointer, long[] termPointers);

  /**
   * Print solution for synthesis conjecture to the given output stream.
   * @param out the output stream
   */
  // TODO: void printSynthSolution(std::ostream& out)

  /**
   * Create a bound variable to be used in a binder (i.e. a quantifier, a
   * lambda, or a witness binder).
   *
   * @param sort   the sort of the variable
   * @param symbol the name of the variable
   * @return the variable
   */
  public Term mkVar(Sort sort, String symbol)
  {
    long termPointer = mkVar(pointer, sort.getPointer(), symbol);
    return new Term(this, termPointer);
  }

  private native long mkVar(long pointer, long sortPointer, String symbol);

  /**
   * Create an uninterpreted sort.
   *
   * @param symbol the name of the sort
   * @return the uninterpreted sort
   */
  public Sort mkUninterpretedSort(String symbol)
  {
    long sortPointer = mkUninterpretedSort(pointer, symbol);
    return new Sort(this, sortPointer);
  }

  private native long mkUninterpretedSort(long pointer, String symbol);

  /**
   * @return sort Integer (in CVC4, Integer is a subtype of Real)
   */
  public Sort getIntegerSort()
  {
    long sortPointer = getIntegerSort(pointer);
    return new Sort(this, sortPointer);
  }

  public native long getIntegerSort(long pointer);

  /**
   * @return null term
   */
  public Term getNullTerm()
  {
    long termPointer = getNullTerm(pointer);
    return new Term(this, termPointer);
  }

  private native long getNullTerm(long pointer);
}
