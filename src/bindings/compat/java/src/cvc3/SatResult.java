package cvc3;

import java.util.*;

/**
 * SatResult is derived from the QueryResult enum in Cvc3, but as we have to
 * use java 1.4 we have to use one of the usual tricks instead of java's Enum.
 * 
 * To be independent of changes of the actual values of the c++ enum elements
 * they are passed by name from the JNI interface, so that changing them will
 * violently break the code (though unfortunately only at runtime).
 */
public class SatResult {
  private final String d_result;

  private SatResult(String result) {
    d_result = result;
  }

  // names of c++ enum values
  public static final SatResult SATISFIABLE = new SatResult("SATISFIABLE");
  public static final SatResult UNSATISFIABLE = new SatResult("UNSATISFIABLE");
  public static final SatResult ABORT = new SatResult("ABORT");
  public static final SatResult UNKNOWN = new SatResult("UNKNOWN");

  // the SatResult corresponding to a c++ enum value by name
  public static SatResult get(String value) throws DebugException {
    if (value.equals(SATISFIABLE.toString())) {
      return SATISFIABLE;
    } else if (value.equals(UNSATISFIABLE.toString())) {
      return UNSATISFIABLE;
    } else if (value.equals(ABORT.toString())) {
      return ABORT;
    } else if (value.equals(UNKNOWN.toString())) {
      return UNKNOWN;
    } else {
      throw new DebugException("SatResult.constructor: unknown enum value: "
          + value);
    }
  }

  // the SatResult's c++ enum value
  public String toString() {
    return d_result;
  }
}
