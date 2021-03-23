package cvc;

import java.lang.ref.Cleaner;

public class DatatypeConstructorDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeConstructorDecl(Solver solver, long pointer)
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
      deletePointer(this.pointer);
    }
  }

  @Override public void close() throws Exception
  {
    System.out.println("Closing datatypeConstructorDecl: " + pointer);
    this.cleanable.clean();
  }

  // endregion

  protected native String toString(long pointer);

  /**
   * Add datatype selector declaration.
   * @param name the name of the datatype selector declaration to add
   * @param sort the range sort of the datatype selector declaration to add
   */
  public void addSelector(String name, Sort sort)
  {
    addSelector(pointer, name, sort.getPointer());
  }

  private native void addSelector(long pointer, String name, long sortPointer);
}
