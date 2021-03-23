package cvc;

abstract public class AbstractPointer implements IPointer
{
  protected final Solver solver;
  protected final long pointer;

  public long getPointer()
  {
    return pointer;
  }

  @Override public String toString()
  {
    return toString(pointer);
  }

  abstract protected String toString(long pointer);

  AbstractPointer(Solver solver, long pointer)
  {
    this.solver = solver;
    this.pointer = pointer;
  }
}
