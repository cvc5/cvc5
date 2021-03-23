package cvc;

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

  // endregion
}
