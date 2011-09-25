package cvc3;

import java.util.*;

/**
 * QueryResult is an enum in Cvc3, but as we have to use java 1.4 we have to
 * use one of the usual tricks instead of java's Enum.
 * 
 * To be independent of changes of the actual values of the c++ enum elements
 * they are passed by name from the JNI interface, so that changing them will
 * violently break the code (though unfortunately only at runtime).
 */
public class QueryResult {
  private final String d_result;

  private QueryResult(String result) {
    d_result = result;
  }

  // value constants
  public static final QueryResult INVALID = new QueryResult("INVALID");
  public static final QueryResult VALID = new QueryResult("VALID");
  public static final QueryResult ABORT = new QueryResult("ABORT");
  public static final QueryResult UNKNOWN = new QueryResult("UNKNOWN");

  // names of c++ enum values, CVC3 maps INVALID->SAT and VALID->UNSAT
  private static Map valueMap = new HashMap() {	  
    {
      put("SATISFIABLE", INVALID);
      put("UNSATISFIABLE", VALID);
      put("UNKNOWN", UNKNOWN);
      put("ABORT", ABORT);
    }
    
	public static final long serialVersionUID = 1L;
  };

  // the QueryResult corresponding to a c++ enum value by name
  public static QueryResult get(String value) throws DebugException {
    QueryResult queryResult = (QueryResult) valueMap.get(value);
    if (queryResult == null) {
      throw new DebugException("QueryResult.constructor: unknown enum value: "
          + value);
    }
    return queryResult;
  }

  public String toString() {
    return d_result;
  }
}
