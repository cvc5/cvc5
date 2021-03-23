package cvc;

import java.io.IOException;
import java.lang.ref.Cleaner;
import java.util.Arrays;

public class Solver implements IPointer
{
  private final long pointer;

  // region cleanup
  private final State state;
  private final Cleaner.Cleanable cleanable;

  public long getPointer()
  {
    return pointer;
  }

  private static class State implements Runnable
  {
    private final long pointer;

    State(long pointer)
    {
      this.pointer = pointer;
    }

    @Override public void run()
    {
      System.out.println("Closing solver: " + pointer);
      deletePointer(this.pointer);
    }
  }

  // endregion

  public Solver()
  {
    this.pointer = newSolver();
    this.state = new State(pointer);
    this.cleanable = Utils.cleaner.register(this, state);
  }

  @Override public void close() throws Exception
  {
    this.cleanable.clean();
  }

  private native long newSolver();

  public void deletePointer()
  {
    deletePointer(pointer);
  }

  private static native void deletePointer(long solverPointer);

  static
  {
    Utils.loadLibraries();
  }

  /**
   * Set logic.
   * SMT-LIB: ( set-logic <symbol> )
   *
   * @param logic
   * @throws CVCApiException
   */
  public void setLogic(String logic) throws CVCApiException
  {
    setLogic(pointer, logic);
  }

  private native void setLogic(long solverPointer, String logic) throws CVCApiException;

  /**
   * @return sort null
   */
  public Sort getNullSort()
  {
    long sortPointer = getNullSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getNullSort(long solverPointer);

  /**
   * @return sort Boolean
   */
  public Sort getBooleanSort()
  {
    long sortPointer = getBooleanSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getBooleanSort(long solverPointer);

  /* Sorts Handling                                                             */
  /* -------------------------------------------------------------------------- */
  // region Sorts Handling

  /**
   * @return sort Integer (in CVC4, Integer is a subtype of Real)
   */
  public Sort getIntegerSort()
  {
    long sortPointer = getIntegerSort(pointer);
    return new Sort(this, sortPointer);
  }

  /**
   * @return sort Real
   */
  public native long getIntegerSort(long solverPointer);

  public Sort getRealSort()
  {
    long sortPointer = getRealSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getRealSort(long solverPointer);

  /**
   * @return sort RegExp
   */
  public Sort getRegExpSort()
  {
    long sortPointer = getRegExpSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getRegExpSort(long solverPointer);

  /**
   * @return sort RoundingMode
   * @throws CVCApiException
   */
  public Sort getRoundingModeSort() throws CVCApiException
  {
    long sortPointer = getRoundingModeSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getRoundingModeSort(long solverPointer) throws CVCApiException;

  /**
   * @return sort String
   */
  public Sort getStringSort()
  {
    long sortPointer = getStringSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getStringSort(long solverPointer);

  // endregion

  public Term mkConst(Sort sort, String symbol)
  {
    long termPointer = mkConst(pointer, sort.getPointer(), symbol);
    return new Term(this, termPointer);
  }

  /* Create sorts ------------------------------------------------------- */
  // region Create sorts

  /**
   * return null sort
   */
  public Sort mkSort()
  {
    long sortPointer = mkSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long mkSort(long pointer);

  /**
   * Create an array sort.
   *
   * @param indexSort   the array index sort
   * @param elementSort the array element sort
   * @return the array sort
   */
  public Sort mkArraySort(Sort indexSort, Sort elementSort)
  {
    long sortPointer = mkArraySort(pointer, indexSort.getPointer(), elementSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkArraySort(
      long solverPointer, long indexSortPointer, long elementSortPointer);

  /**
   * Create a bit-vector sort.
   *
   * @param size the bit-width of the bit-vector sort
   * @return the bit-vector sort
   */
  public Sort mkBitVectorSort(int size) throws CVCApiException
  {
    if (size < 0)
    {
      throw new CVCApiException("Expected size '" + size + "' to be non negative.");
    }
    long sortPointer = mkBitVectorSort(pointer, size);
    return new Sort(this, sortPointer);
  }

  private native long mkBitVectorSort(long solverPointer, int size);

  /**
   * Create a floating-point sort.
   *
   * @param exp the bit-width of the exponent of the floating-point sort.
   * @param sig the bit-width of the significand of the floating-point sort.
   */
  public Sort mkFloatingPointSort(int exp, int sig) throws CVCApiException
  {
    if (exp < 0)
    {
      throw new CVCApiException("Expected expr '" + exp + "' to be non negative.");
    }
    if (sig < 0)
    {
      throw new CVCApiException("Expected sig '" + sig + "' to be non negative.");
    }
    long sortPointer = mkFloatingPointSort(pointer, exp, sig);
    return new Sort(this, sortPointer);
  }

  private native long mkFloatingPointSort(long solverPointer, int exp, int sig)
      throws CVCApiException;

  /**
   * Create a datatype sort.
   *
   * @param datatypeDecl the datatype declaration from which the sort is created
   * @return the datatype sort
   */
  public Sort mkDatatypeSort(DatatypeDecl datatypeDecl) throws CVCApiException
  {
    long pointer = mkDatatypeSort(this.pointer, datatypeDecl.getPointer());
    return new Sort(this, pointer);
  }

  private native long mkDatatypeSort(long solverPointer, long datatypeDeclPointer)
      throws CVCApiException;

  /**
   * Create a vector of datatype sorts. The names of the datatype declarations
   * must be distinct.
   *
   * @param datatypeDecls the datatype declarations from which the sort is created
   * @return the datatype sorts
   */
  public Sort[] mkDatatypeSorts(DatatypeDecl[] datatypeDecls) throws CVCApiException
  {
    long[] declPointers = new long[datatypeDecls.length];
    for (int i = 0; i < datatypeDecls.length; i++)
    {
      declPointers[i] = datatypeDecls[i].getPointer();
    }

    long[] sortPointers = mkDatatypeSorts(pointer, declPointers);

    Sort[] sorts = new Sort[sortPointers.length];
    for (int i = 0; i < sortPointers.length; i++)
    {
      sorts[i] = new Sort(this, sortPointers[i]);
    }

    return sorts;
  }

  private native long[] mkDatatypeSorts(long solverPointer, long[] declPointers)
      throws CVCApiException;

  /**
   * Create a vector of datatype sorts using unresolved sorts. The names of
   * the datatype declarations in dtypedecls must be distinct.
   * <p>
   * This method is called when the DatatypeDecl objects dtypedecls have been
   * built using "unresolved" sorts.
   * <p>
   * We associate each sort in unresolvedSorts with exactly one datatype from
   * dtypedecls. In particular, it must have the same name as exactly one
   * datatype declaration in dtypedecls.
   * <p>
   * When constructing datatypes, unresolved sorts are replaced by the datatype
   * sort constructed for the datatype declaration it is associated with.
   *
   * @param dtypedecls      the datatype declarations from which the sort is created
   * @param unresolvedSorts the list of unresolved sorts
   * @return the datatype sorts
   */
  public Sort[] mkDatatypeSorts(DatatypeDecl[] dtypedecls, Sort[] unresolvedSorts)
      throws CVCApiException
  {
    long[] declPointers = Utils.getPointers(dtypedecls);
    long[] unresolvedPointers = Utils.getPointers(unresolvedSorts);
    long[] sortPointers = mkDatatypeSorts(pointer, declPointers, unresolvedPointers);
    Sort[] sorts = Utils.getSorts(this, sortPointers);
    return sorts;
  }

  private native long[] mkDatatypeSorts(
      long pointer, long[] declPointers, long[] unresolvedPointers) throws CVCApiException;

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

  private native long mkUninterpretedSort(long solverPointer, String symbol);

  /**
   * Create function sort.
   *
   * @param domain   the sort of the fuction argument
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  public Sort mkFunctionSort(Sort domain, Sort codomain)
  {
    long sortPointer = mkFunctionSort(pointer, domain.getPointer(), codomain.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkFunctionSort(long pointer, long domainPointer, long codomainPointer);

  /**
   * Create function sort.
   *
   * @param sorts    the sort of the function arguments
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  public Sort mkFunctionSort(Sort[] sorts, Sort codomain)
  {
    long sortPointer = mkFunctionSort(pointer, Utils.getPointers(sorts), codomain.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkFunctionSort(long pointer, long[] sortPointers, long codomainPointer);

  /**
   * Create a sort parameter.
   *
   * @param symbol the name of the sort
   * @return the sort parameter
   */
  public Sort mkParamSort(String symbol)
  {
    long sortPointer = mkParamSort(pointer, symbol);
    return new Sort(this, sortPointer);
  }

  private native long mkParamSort(long pointer, String symbol);

  /**
   * Create a predicate sort.
   *
   * @param sorts the list of sorts of the predicate
   * @return the predicate sort
   */
  public Sort mkPredicateSort(Sort[] sorts)
  {
    long sortPointer = mkPredicateSort(pointer, Utils.getPointers(sorts));
    return new Sort(this, sortPointer);
  }

  private native long mkPredicateSort(long pointer, long[] sortPointers);

  /**
   * Create a record sort
   *
   * @param fields the list of fields of the record
   * @return the record sort
   */
  public Sort mkRecordSort(Pair<String, Sort>[] fields)
  {
    long sortPointer = mkRecordSort(pointer, Utils.getPairs(fields));
    return new Sort(this, sortPointer);
  }

  private native long mkRecordSort(long pointer, Pair<String, Long>[] fields);

  /**
   * Create a set sort.
   *
   * @param elementSort the sort of the set elements
   * @return the set sort
   */
  public Sort mkSetSort(Sort elementSort)
  {
    long sortPointer = mkSetSort(pointer, elementSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkSetSort(long pointer, long elementSortPointer);

  /**
   * Create a bag sort.
   *
   * @param elementSort the sort of the bag elements
   * @return the bag sort
   */
  public Sort mkBagSort(Sort elementSort)
  {
    long sortPointer = mkBagSort(pointer, elementSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkBagSort(long pointer, long elementSortPointer);

  /**
   * Create a sequence sort.
   *
   * @param elementSort the sort of the sequence elements
   * @return the sequence sort
   */
  public Sort mkSequenceSort(Sort elementSort)
  {
    long sortPointer = mkSequenceSort(pointer, elementSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkSequenceSort(long pointer, long elementSortPointer);

  /**
   * Create a sort constructor sort.
   *
   * @param symbol the symbol of the sort
   * @param arity  the arity of the sort
   * @return the sort constructor sort
   */
  public Sort mkSortConstructorSort(String symbol, int arity) throws CVCApiException
  {
    if (arity < 0)
    {
      throw new CVCApiException("Expected arity '" + arity + "' to be non negative.");
    }
    long sortPointer = mkSortConstructorSort(pointer, symbol, arity);
    return new Sort(this, sortPointer);
  }

  private native long mkSortConstructorSort(long pointer, String symbol, int arity);

  /**
   * Create a tuple sort.
   *
   * @param sorts of the elements of the tuple
   * @return the tuple sort
   */
  public Sort mkTupleSort(Sort[] sorts)
  {
    long sortPointer = mkTupleSort(pointer, Utils.getPointers(sorts));
    return new Sort(this, sortPointer);
  }

  private native long mkTupleSort(long pointer, long[] sortPointers);

  // endregion

  private native long mkConst(long solverPointer, long sortPointer, String symbol);

  public Result checkSat()
  {
    long resultPointer = checkSat(pointer);
    return new Result(this, resultPointer);
  }

  /* .................................................................... */
  /* Create Terms                                                         */
  /* .................................................................... */
  // region Create Terms

  /**
   * return null term
   */
  public Term mkTerm()
  {
    long termPointer = mkTerm(pointer);
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer);

  /**
   * Create 0-ary term of given kind.
   *
   * @param kind the kind of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind)
  {
    long termPointer = mkTermKind(pointer, kind.getValue());
    return new Term(this, termPointer);
  }

  private native long mkTermKind(long pointer, int kind);

  /**
   * Create a unary term of given kind.
   *
   * @param kind  the kind of the term
   * @param child the child of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term child)
  {
    long termPointer = mkTermChild(pointer, kind.getValue(), child.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTermChild(long pointer, long kind, long termPointer);

  /**
   * Create binary term of given kind.
   *
   * @param kind   the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term child1, Term child2)
  {
    long termPointer = mkTerm(pointer, kind.getValue(), child1.getPointer(), child2.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long solverPointer, int kind, long child1Pointer, long child2Pointer);

  /**
   * Create ternary term of given kind.
   *
   * @param kind   the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @param child3 the third child of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term child1, Term child2, Term child3)
  {
    long termPointer = mkTerm(
        pointer, kind.getValue(), child1.getPointer(), child2.getPointer(), child3.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(
      long solverPointer, int kind, long child1Pointer, long child2Pointer, long child3Pointer);

  /**
   * Create n-ary term of given kind.
   *
   * @param kind     the kind of the term
   * @param children the children of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term[] children)
  {
    long termPointer = mkTerm(pointer, kind.getValue(), Utils.getPointers(children));
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, int kind, long[] childrenPointers);

  private native long checkSat(long solverPointer);

  public void assertFormula(Term term)
  {
    assertFormula(pointer, term.getPointer());
  }

  private native void assertFormula(long solverPointer, long termPointer);

  public void push()
  {
    push(pointer, 1);
  }

  public void push(int nscopes)
  {
    push(pointer, nscopes);
  }

  private native void push(long solverPointer, int nscopes);

  public Result checkEntailed(Term term)
  {
    long resultPointer = checkEntailed(pointer, term.getPointer());
    return new Result(this, resultPointer);
  }

  private native long checkEntailed(long solverPointer, long termPointer);

  public void pop()
  {
    pop(pointer, 1);
  }

  public void pop(int nscopes)
  {
    pop(pointer, nscopes);
  }

  private native void pop(long solverPointer, int nscopes);

  /**
   * Set option.
   * SMT-LIB: ( set-option <option> )
   *
   * @param option option the option name
   * @param value  the option value
   * @throws CVCApiException
   */
  public void setOption(String option, String value) throws CVCApiException
  {
    setOption(pointer, option, value);
  }

  private native void setOption(long solverPointer, String option, String value)
      throws CVCApiException;

  /**
   * Get the value of the given term.
   * SMT-LIB: ( get-value ( <term> ) )
   *
   * @param term term the term for which the value is queried
   * @return the value of the given term
   */
  public Term getValue(Term term) throws CVCApiRecoverableException
  {
    long termPointer = getValue(pointer, term.getPointer());
    return new Term(this, termPointer);
  }

  private native long getValue(long solverPointer, long termPointer)
      throws CVCApiRecoverableException;

  public boolean supportsFloatingPoint()
  {
    return supportsFloatingPoint(pointer);
  }

  private native boolean supportsFloatingPoint(long solverPointer);

  /**
   * Create a roundingmode constant.
   *
   * @param rm the floating point rounding mode this constant represents
   */
  public Term mkRoundingMode(RoundingMode rm) throws CVCApiException
  {
    long termPointer = mkRoundingMode(pointer, rm.getValue());
    return new Term(this, termPointer);
  }

  private native long mkRoundingMode(long solverPointer, int value) throws CVCApiException;
  /* -------------------------------------------------------------------------- */
  /* Create datatype declarations                                               */
  /* -------------------------------------------------------------------------- */
  // region Create datatype declarations

  /**
   * Create a datatype declaration.
   *
   * @param name the name of the datatype
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name)
  {
    return mkDatatypeDecl(name, false);
  }

  /**
   * Create a datatype declaration.
   *
   * @param name         the name of the datatype
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, boolean isCoDatatype)
  {
    long pointer = mkDatatypeDecl(this.pointer, name, isCoDatatype);
    return new DatatypeDecl(this, pointer);
  }

  private native long mkDatatypeDecl(long solverPointer, String name, boolean isCoDatatype);

  public DatatypeConstructorDecl mkDatatypeConstructorDecl(String name)
  {
    long pointer = mkDatatypeConstructorDecl(this.pointer, name);
    return new DatatypeConstructorDecl(this, pointer);
  }

  private native long mkDatatypeConstructorDecl(long solverPointer, String name);

  // endregion

  /* .................................................................... */
  /* Create Operators                                                     */
  /* .................................................................... */
  // region Create Operators

  /**
   * return null operator
   */
  public Op mkOp()
  {
    long opPointer = mkOp(pointer);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer);

  /**
   * Create an operator for a builtin Kind
   * The Kind may not be the Kind for an indexed operator
   * (e.g. BITVECTOR_EXTRACT)
   * Note: in this case, the Op simply wraps the Kind.
   * The Kind can be used in mkTerm directly without
   * creating an op first.
   *
   * @param kind the kind to wrap
   */
  public Op mkOp(Kind kind)
  {
    long opPointer = mkOp(pointer, kind.getValue());
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kind);

  /**
   * Create operator of kind:
   * - RECORD_UPDATE
   * - DIVISIBLE (to support arbitrary precision integers)
   * See enum Kind for a description of the parameters.
   *
   * @param kind the kind of the operator
   * @param arg  the string argument to this operator
   */
  public Op mkOp(Kind kind, String arg)
  {
    long opPointer = mkOp(pointer, kind.getValue(), arg);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int value, String arg);

  /**
   * Create operator of kind:
   * - DIVISIBLE
   * - BITVECTOR_REPEAT
   * - BITVECTOR_ZERO_EXTEND
   * - BITVECTOR_SIGN_EXTEND
   * - BITVECTOR_ROTATE_LEFT
   * - BITVECTOR_ROTATE_RIGHT
   * - INT_TO_BITVECTOR
   * - FLOATINGPOINT_TO_UBV
   * - FLOATINGPOINT_TO_UBV_TOTAL
   * - FLOATINGPOINT_TO_SBV
   * - FLOATINGPOINT_TO_SBV_TOTAL
   * - TUPLE_UPDATE
   * See enum Kind for a description of the parameters.
   *
   * @param kind the kind of the operator
   * @param arg  the uint32_t argument to this operator
   */
  public Op mkOp(Kind kind, int arg) throws CVCApiException
  {
    if (arg < 0)
    {
      throw new CVCApiException("Expected arg '" + arg + "' to be non negative.");
    }
    long opPointer = mkOp(pointer, kind.getValue(), arg);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kind, int arg);

  /**
   * Create operator of Kind:
   * - BITVECTOR_EXTRACT
   * - FLOATINGPOINT_TO_FP_IEEE_BITVECTOR
   * - FLOATINGPOINT_TO_FP_FLOATINGPOINT
   * - FLOATINGPOINT_TO_FP_REAL
   * - FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR
   * - FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR
   * - FLOATINGPOINT_TO_FP_GENERIC
   * See enum Kind for a description of the parameters.
   *
   * @param kind the kind of the operator
   * @param arg1 the first uint32_t argument to this operator
   * @param arg2 the second uint32_t argument to this operator
   */
  public Op mkOp(Kind kind, int arg1, int arg2) throws CVCApiException
  {
    if (arg1 < 0)
    {
      throw new CVCApiException("Expected arg1 '" + arg1 + "' to be non negative.");
    }
    if (arg2 < 0)
    {
      throw new CVCApiException("Expected arg2 '" + arg2 + "' to be non negative.");
    }
    long opPointer = mkOp(pointer, kind.getValue(), arg1, arg2);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int value, int arg1, int arg2);

  // endregion

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */
  // region Create Constants

  /**
   * Create a Boolean true constant.
   *
   * @return the true constant
   */
  public Term mkTrue()
  {
    long termPointer = mkTrue(pointer);
    return new Term(this, termPointer);
  }

  private native long mkTrue(long solverPointer);

  /**
   * Create a Boolean false constant.
   *
   * @return the false constant
   */
  public Term mkFalse()
  {
    long termPointer = mkFalse(pointer);
    return new Term(this, termPointer);
  }

  private native long mkFalse(long solverPointer);

  /**
   * Create a Boolean constant.
   *
   * @param val the value of the constant
   * @return the Boolean constant
   */
  public Term mkBoolean(boolean val)
  {
    long termPointer = mkBoolean(pointer, val);
    return new Term(this, termPointer);
  }

  private native long mkBoolean(long pointer, boolean val);

  /**
   * Create a constant representing the number Pi.
   *
   * @return a constant representing Pi
   */
  public Term mkPi()
  {
    long termPointer = mkPi(pointer);
    return new Term(this, termPointer);
  }

  private native long mkPi(long pointer);

  /**
   * Create an integer constant from a string.
   *
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123").
   * @return a constant of sort Integer assuming 's' represents an integer)
   */
  public Term mkInteger(String s) throws CVCApiException
  {
    long termPointer = mkInteger(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkInteger(long pointer, String s) throws CVCApiException;

  /**
   * Create an integer constant from a c++ int.
   *
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  public Term mkInteger(long val)
  {
    long termPointer = mkInteger(pointer, val);
    return new Term(this, termPointer);
  }

  private native long mkInteger(long pointer, long val);

  /**
   * Create a real constant from a string.
   *
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123") or real constant (e.g., "12.34" or "12/34").
   * @return a constant of sort Real
   */
  public Term mkReal(String s) throws CVCApiException
  {
    long termPointer = mkReal(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkReal(long pointer, String s) throws CVCApiException;

  /**
   * Create a real constant from an integer.
   *
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  public Term mkReal(long val)
  {
    long termPointer = mkRealVal(pointer, val);
    return new Term(this, termPointer);
  }

  private native long mkRealVal(long pointer, long val);

  /**
   * Create a real constant from a rational.
   *
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real
   */
  public Term mkReal(long num, long den)
  {
    long termPointer = mkReal(pointer, num, den);
    return new Term(this, termPointer);
  }

  private native long mkReal(long pointer, long num, long den);

  /**
   * Create a regular expression empty term.
   *
   * @return the empty term
   */
  public Term mkRegexpEmpty()
  {
    long termPointer = mkRegexpEmpty(pointer);
    return new Term(this, termPointer);
  }

  private native long mkRegexpEmpty(long pointer);

  /**
   * Create a regular expression sigma term.
   *
   * @return the sigma term
   */
  public Term mkRegexpSigma()
  {
    long termPointer = mkRegexpSigma(pointer);
    return new Term(this, termPointer);
  }

  private native long mkRegexpSigma(long pointer);

  /**
   * Create a constant representing an empty set of the given sort.
   *
   * @param s the sort of the set elements.
   * @return the empty set constant
   */
  public Term mkEmptySet(Sort s)
  {
    long termPointer = mkEmptySet(pointer, s.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkEmptySet(long pointer, long sortPointer);

  /**
   * Create a constant representing an empty bag of the given sort.
   *
   * @param s the sort of the bag elements.
   * @return the empty bag constant
   */
  public Term mkEmptyBag(Sort s)
  {
    long termPointer = mkEmptyBag(pointer, s.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkEmptyBag(long pointer, long sortPointer);

  /**
   * Create a separation logic nil term.
   *
   * @param sort the sort of the nil term
   * @return the separation logic nil term
   */
  public Term mkSepNil(Sort sort)
  {
    long termPointer = mkSepNil(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkSepNil(long pointer, long sortPointer);

  /**
   * Create a String constant.
   *
   * @param s the string this constant represents
   * @return the String constant
   */
  public Term mkString(String s)
  {
    long termPointer = mkString(pointer, s, false);
    return new Term(this, termPointer);
  }

  /**
   * Create a String constant.
   *
   * @param s               the string this constant represents
   * @param useEscSequences determines whether escape sequences in \p s should
   *                        be converted to the corresponding character
   * @return the String constant
   */
  public Term mkString(String s, boolean useEscSequences)
  {
    long termPointer = mkString(pointer, s, useEscSequences);
    return new Term(this, termPointer);
  }

  private native long mkString(long pointer, String s, boolean useEscSequences);

  /**
   * Create a String constant.
   *
   * @param c the character this constant represents
   * @return the String constant
   */
  public Term mkString(byte c)
  {
    long termPointer = mkString(pointer, c);
    return new Term(this, termPointer);
  }

  private native long mkString(long pointer, byte c);

  /**
   * Create a String constant.
   *
   * @param s a list of unsigned values this constant represents as string
   * @return the String constant
   */
  public Term mkString(byte[] s) throws CVCApiException
  {
    // make sure the integers are unsigned
    for (int i : s)
    {
      if (i < 0)
      {
        throw new CVCApiException("Value " + i + " in array" + s + " should be non negative.");
      }
    }

    long termPointer = mkString(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkString(long pointer, byte[] s);

  /**
   * Create a character constant from a given string.
   *
   * @param s the string denoting the code point of the character (in base 16)
   * @return the character constant
   */
  public Term mkChar(String s)
  {
    long termPointer = mkChar(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkChar(long pointer, String s);

  /**
   * Create an empty sequence of the given element sort.
   *
   * @param sort The element sort of the sequence.
   * @return the empty sequence with given element sort.
   */
  public Term mkEmptySequence(Sort sort)
  {
    long termPointer = mkEmptySequence(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkEmptySequence(long pointer, long sortPointer);

  public Term mkBitVector(int size) throws CVCApiException
  {
    return mkBitVector(size, 0);
  }

  /**
   * Create a bit-vector constant of given size and value.
   *
   * @param size the bit-width of the bit-vector sort
   * @param val  the value of the constant
   * @return the bit-vector constant
   */
  public Term mkBitVector(int size, long val) throws CVCApiException
  {
    if (size < 0)
    {
      throw new CVCApiException("Expected size '" + size + "' to be non negative.");
    }
    if (val < 0)
    {
      throw new CVCApiException("Expected val '" + val + "' to be non negative.");
    }
    long termPointer = mkBitVector(pointer, size, val);
    return new Term(this, termPointer);
  }

  private native long mkBitVector(long pointer, int size, long val) throws CVCApiException;

  public Term mkBitVector(String s) throws CVCApiException
  {
    return mkBitVector(s, 2);
  }

  /**
   * Create a bit-vector constant from a given string of base 2, 10 or 16.
   * <p>
   * The size of resulting bit-vector is
   * - base  2: the size of the binary string
   * - base 10: the min. size required to represent the decimal as a bit-vector
   * - base 16: the max. size required to represent the hexadecimal as a
   * bit-vector (4 * size of the given value string)
   *
   * @param s    the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  public Term mkBitVector(String s, int base) throws CVCApiException
  {
    if (base < 0)
    {
      throw new CVCApiException("Expected base '" + base + "' to be non negative.");
    }
    long termPointer = mkBitVector(pointer, s, base);
    return new Term(this, termPointer);
  }

  private native long mkBitVector(long pointer, String s, int base);

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * @param size the bit-width of the constant
   * @param s    the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  public Term mkBitVector(int size, String s, int base) throws CVCApiException
  {
    if (size < 0)
    {
      throw new CVCApiException("Expected size '" + size + "' to be non negative.");
    }
    if (base < 0)
    {
      throw new CVCApiException("Expected base '" + base + "' to be non negative.");
    }
    long termPointer = mkBitVector(pointer, size, s, base);
    return new Term(this, termPointer);
  }

  private native long mkBitVector(long pointer, int size, String s, int base);

  /**
   * Create a constant array with the provided constant value stored at every
   * index
   *
   * @param sort the sort of the constant array (must be an array sort)
   * @param val  the constant value to store (must match the sort's element sort)
   * @return the constant array term
   */
  public Term mkConstArray(Sort sort, Term val)
  {
    long termPointer = mkConstArray(pointer, sort.getPointer(), val.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkConstArray(long pointer, long sortPointer, long valPointer);

  /**
   * Create a positive infinity floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   *
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkPosInf(int exp, int sig) throws CVCApiException
  {
    if (exp < 0)
    {
      throw new CVCApiException("Expected exp '" + exp + "' to be non negative.");
    }
    if (sig < 0)
    {
      throw new CVCApiException("Expected sig '" + sig + "' to be non negative.");
    }
    long termPointer = mkPosInf(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkPosInf(long pointer, int exp, int sig);

  /**
   * Create a negative infinity floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   *
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNegInf(int exp, int sig) throws CVCApiException
  {
    if (exp < 0)
    {
      throw new CVCApiException("Expected exp '" + exp + "' to be non negative.");
    }
    if (sig < 0)
    {
      throw new CVCApiException("Expected sig '" + sig + "' to be non negative.");
    }
    long termPointer = mkNegInf(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkNegInf(long pointer, int exp, int sig);

  /**
   * Create a not-a-number (NaN) floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   *
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNaN(int exp, int sig) throws CVCApiException
  {
    if (exp < 0)
    {
      throw new CVCApiException("Expected exp '" + exp + "' to be non negative.");
    }
    if (sig < 0)
    {
      throw new CVCApiException("Expected sig '" + sig + "' to be non negative.");
    }
    long termPointer = mkNaN(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkNaN(long pointer, int exp, int sig);

  /**
   * Create a positive zero (+0.0) floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   *
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkPosZero(int exp, int sig) throws CVCApiException
  {
    if (exp < 0)
    {
      throw new CVCApiException("Expected exp '" + exp + "' to be non negative.");
    }
    if (sig < 0)
    {
      throw new CVCApiException("Expected sig '" + sig + "' to be non negative.");
    }
    long termPointer = mkPosZero(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkPosZero(long pointer, int exp, int sig);

  /**
   * Create a negative zero (-0.0) floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   *
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNegZero(int exp, int sig) throws CVCApiException
  {
    if (exp < 0)
    {
      throw new CVCApiException("Expected exp '" + exp + "' to be non negative.");
    }
    if (sig < 0)
    {
      throw new CVCApiException("Expected sig '" + sig + "' to be non negative.");
    }
    long termPointer = mkNegZero(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkNegZero(long pointer, int exp, int sig);

  /**
   * Create uninterpreted constant.
   *
   * @param sort  Sort of the constant
   * @param index Index of the constant
   */
  public Term mkUninterpretedConst(Sort sort, int index)
  {
    long termPointer = mkUninterpretedConst(pointer, sort.getPointer(), index);
    return new Term(this, termPointer);
  }

  private native long mkUninterpretedConst(long pointer, long sortPointer, int index);

  /**
   * Create an abstract value constant.
   *
   * @param index Index of the abstract value
   */
  public Term mkAbstractValue(String index)
  {
    long termPointer = mkAbstractValue(pointer, index);
    return new Term(this, termPointer);
  }

  private native long mkAbstractValue(long pointer, String index);

  /**
   * Create an abstract value constant.
   *
   * @param index Index of the abstract value
   */
  public Term mkAbstractValue(long index)
  {
    long termPointer = mkAbstractValue(pointer, index);
    return new Term(this, termPointer);
  }

  private native long mkAbstractValue(long pointer, long index);

  /**
   * Create a floating-point constant (requires CVC4 to be compiled with symFPU
   * support).
   *
   * @param exp Size of the exponent
   * @param sig Size of the significand
   * @param val Value of the floating-point constant as a bit-vector term
   */
  public Term mkFloatingPoint(int exp, int sig, Term val)
  {
    long termPointer = mkFloatingPoint(pointer, exp, sig, val.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkFloatingPoint(long pointer, int exp, int sig, long termPointer);

  // endregion

  /* -------------------------------------------------------------------------- */
  /* Create variables                                                           */
  /* -------------------------------------------------------------------------- */
  // region Create Variables

  public Term mkVar(Sort sort)
  {
    return mkVar(sort, "");
  }

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

  // endregion
}
