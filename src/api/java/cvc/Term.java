package cvc;

import java.lang.ref.Cleaner;

public class Term extends AbstractPointer
{
  // region construction and destruction
  Term(Solver solver, long pointer)
  {
    super(solver, pointer);
    State state = new State(pointer);
    this.cleanable = Utils.cleaner.register(this, state);
  }

  protected static native void deletePointer(long pointer);

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
      System.out.println("Closing term: " + pointer);
      deletePointer(this.pointer);
    }
  }

  @Override public void close() throws Exception
  {
    this.cleanable.clean();
  }

  // endregion

  protected native String toString(long pointer);

  @Override public boolean equals(Object term)
  {
    if (this == term)
      return true;
    if (term == null || getClass() != term.getClass())
      return false;
    return equals(pointer, ((Term) term).pointer);
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Equality.
   * @param t a Boolean term
   * @return the Boolean equivalence of this term and the given term
   */
  public Term eqTerm(Term t) throws CVCApiException
  {
    long pointer = eqTerm(this.pointer, t.pointer);
    return new Term(solver, pointer);
  }

  private native long eqTerm(long termPointer, long tPointer) throws CVCApiException;

  /**
   * Boolean negation.
   * @return the Boolean negation of this term
   */
  public Term notTerm() throws CVCApiException
  {
    long pointer = notTerm(this.pointer);
    return new Term(solver, pointer);
  }

  private native long notTerm(long termPointer) throws CVCApiException;
}
