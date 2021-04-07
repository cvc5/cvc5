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

  /**
   * Set logic.
   * SMT-LIB: ( set-logic <symbol> )
   *
   * @param logic
   * @throws CVC5ApiException
   */
  public void setLogic(String logic) throws CVC5ApiException
  {
    setLogic(pointer, logic);
  }

  private native void setLogic(long pointer, String logic) throws CVC5ApiException;

  // endregion

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
