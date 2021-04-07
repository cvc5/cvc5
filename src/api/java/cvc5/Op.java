package cvc5;

public class Op extends AbstractPointer
{
  // region construction and destruction
  Op(Solver solver, long pointer)
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
   * @return a string representation of this operator
   */
  protected native String toString(long pointer);
}