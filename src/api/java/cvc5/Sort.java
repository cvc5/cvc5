package cvc5;

public class Sort extends AbstractPointer
{
  // region construction and destruction
  Sort(Solver solver, long pointer)
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
   * @return a string representation of this sort
   */
  protected native String toString(long pointer);
}