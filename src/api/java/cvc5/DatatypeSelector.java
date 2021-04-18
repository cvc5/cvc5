package cvc5;

public class DatatypeSelector extends AbstractPointer
{
  // region construction and destruction
  DatatypeSelector(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /** @return the name of this Datatype selector. */
  String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

  /**
   * Get the selector operator of this datatype selector.
   * @return the selector term
   */
  public Term getSelectorTerm()
  {
    long termPointer = getSelectorTerm(pointer);
    return new Term(solver, termPointer);
  }

  private native long getSelectorTerm(long pointer);

  /** @return the range sort of this argument. */
  Sort getRangeSort()
  {
    long sortPointer = getRangeSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getRangeSort(long pointer);

  /**
   * @return true if this DatatypeSelector is a null object
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return a string representation of this datatype selector
   */
  protected native String toString(long pointer);
}
