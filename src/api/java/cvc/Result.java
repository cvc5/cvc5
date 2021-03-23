package cvc;

import java.lang.ref.Cleaner;

public class Result extends AbstractPointer
{
  // region construction and destruction
  Result(Solver solver, long pointer)
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
      System.out.println("Closing result: " + pointer);
      deletePointer(this.pointer);
    }
  }

  @Override public void close() throws Exception
  {
    this.cleanable.clean();
  }

  // endregion

  protected native String toString(long pointer);
}
