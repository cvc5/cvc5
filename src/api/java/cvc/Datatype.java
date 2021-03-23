package cvc;

import java.lang.ref.Cleaner;

public class Datatype extends AbstractPointer
{
  // region construction and destruction
  Datatype(Solver solver, long pointer)
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
    System.out.println("Closing datatype: " + pointer);
    this.cleanable.clean();
  }

  // endregion

  protected native String toString(long pointer);
}
