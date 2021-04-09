package cvc5;

public class DatatypeConstructor extends AbstractPointer
{
  // region construction and destruction
  DatatypeConstructor(Solver solver, long pointer)
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
   * @return a string representation of this datatype constructor
   */
  protected native String toString(long pointer);
}
