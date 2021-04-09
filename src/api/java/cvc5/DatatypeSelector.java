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

  /**
   * @return a string representation of this datatype selector
   */
  protected native String toString(long pointer);
}
