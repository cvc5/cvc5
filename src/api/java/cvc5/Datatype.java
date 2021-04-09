package cvc5;

import java.lang.ref.Cleaner;

public class Datatype extends AbstractPointer
{
  // region construction and destruction
  Datatype(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  protected native String toString(long pointer);
}
