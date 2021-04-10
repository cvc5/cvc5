package cvc5;

import java.util.Map;
import java.util.HashMap;

public class Result extends AbstractPointer
{
  // region construction and destruction
  Result(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  public enum UnknownExplanation
  {
    REQUIRES_FULL_CHECK (0),
    INCOMPLETE (1),
    TIMEOUT (2),
    RESOURCEOUT(3),
    MEMOUT (4),
    INTERRUPTED (5),
    NO_STATUS (6),
    UNSUPPORTED (7),
    OTHER (8),
    UNKNOWN_REASON (9);

     /* the int value of the UnknownExplanation */
      private int value;
      private static Map<Integer, UnknownExplanation> explanationMap = new HashMap<>();
      private UnknownExplanation(int value)
      {
        this.value = value;
      }

      static
      {
        for (UnknownExplanation explanation : UnknownExplanation.values())
        {
          explanationMap.put(explanation.getValue(), explanation);
        }
      }

      public static UnknownExplanation fromInt(int value) throws CVC5ApiException
      {
        if (value < REQUIRES_FULL_CHECK.value || value > UNKNOWN_REASON.value)
        {
          throw new CVC5ApiException("UnknownExplanation value " + value + " is outside the valid range ["
              + REQUIRES_FULL_CHECK.value + "," + UNKNOWN_REASON.value + "]");
        }
        return explanationMap.get(value);
      }

      public int getValue()
      {
        return value;
      }
  }

  /**
   * Return true if Result is empty, i.e., a nullary Result, and not an actual
   * result returned from a checkSat() (and friends) query.
   */
  public boolean  isNull()
  {
    return isNull(pointer);
  }
   
  private native boolean isNull(long pointer);

  /**
   * Return true if query was a satisfiable checkSat() or checkSatAssuming()
   * query.
   */
  public boolean  isSat()
  {
    return isSat(pointer);
  }

  private native boolean isSat(long pointer);

  /**
   * Return true if query was an unsatisfiable checkSat() or
   * checkSatAssuming() query.
   */
  public boolean isUnsat()
  {
    return isUnsat(pointer);
  }

  private native boolean isUnsat(long pointer);

  /**
   * Return true if query was a checkSat() or checkSatAssuming() query and
   * CVC4 was not able to determine (un)satisfiability.
   */
  public boolean  isSatUnknown()
  {
    return isSatUnknown(pointer);
  }

  private native boolean isSatUnknown(long pointer);

  /**
   * Return true if corresponding query was an entailed checkEntailed() query.
   */
  public boolean  isEntailed()
  {
    return isEntailed(pointer);
  }

  private native boolean isEntailed(long pointer);

  /**
   * Return true if corresponding query was a checkEntailed() query that is
   * not entailed.
   */
  public boolean  isNotEntailed()
  {
      return isNotEntailed(pointer);
  }

  private native boolean isNotEntailed(long pointer);

  /**
   * Return true if query was a checkEntailed() () query and CVC4 was not able
   * to determine if it is entailed.
   */
  public boolean  isEntailmentUnknown()
  {
    return isEntailmentUnknown(pointer);
  }

  private native boolean isEntailmentUnknown(long pointer);

  /**
   * Operator overloading for equality of two results.
   * @param r the result to compare to for equality
   * @return true if the results are equal
   */
  @Override public boolean equals(Object r)
    {
      if (this == r)
        return true;
      if (r == null || getClass() != r.getClass())
        return false;
      return equals(pointer, ((Result) r).getPointer());
    }

    private native boolean equals(long pointer1, long pointer2);

  /**
   * @return an explanation for an unknown query result.
   */
  public UnknownExplanation getUnknownExplanation()
  {
    try
    {
      int explanation = getUnknownExplanation(pointer);
      return UnknownExplanation.fromInt(explanation);
    }
    catch(CVC5ApiException e)
    {
      e.printStackTrace();
      throw new RuntimeException(e.getMessage());
    }
  }

  private native int getUnknownExplanation(long pointer);

  /**
   * @return a string representation of this result.
   */
  protected native String toString(long pointer);
}
