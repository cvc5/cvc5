package cvc;

import java.lang.ref.Cleaner;

public class DatatypeDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeDecl(Solver solver, long pointer)
  {
    super(solver, pointer);
    this.state = new State(pointer);
    this.cleanable = Utils.cleaner.register(this, state);
  }

  protected static native void deletePointer(long pointer);

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
      System.out.println("Closing datatypeDecl: " + pointer);
      deletePointer(this.pointer);
    }
  }

  @Override public void close() throws Exception
  {
    this.cleanable.clean();
  }

  // endregion

  protected native String toString(long pointer);

  /**
   * Add datatype constructor declaration.
   * @param ctor the datatype constructor declaration to add
   */
  public void addConstructor(DatatypeConstructorDecl ctor)
  {
    addConstructor(pointer, ctor.getPointer());
  }

  private native void addConstructor(long pointer, long datatypeConstructorDeclPointer);
}
