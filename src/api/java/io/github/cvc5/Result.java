/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.util.HashMap;
import java.util.Map;

/**
 * Encapsulation of a three-valued solver result, with explanations.
 */
public class Result extends AbstractPointer
{
  /**
   * Null result
   */
  public Result()
  {
    super(null, 0, null);
  }

  Result(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, Result::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_result_release(pointer);
  }

  /**
   * Determine if Result is empty, i.e., a nullary Result, and not an actual
   * result returned from a checkSat() (and friends) query.
   *
   * @return True if Result is empty, i.e., a nullary Result, and not an actual
   * result returned from a checkSat() (and friends) query.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private boolean isNull(long pointer)
  {
    return pointer == 0 || CApi.cvc5_result_is_null(pointer);
  }

  /**
   * Determine if query was a satisfiable checkSat() or checkSatAssuming()
   * query.
   *
   * @return True if query was a satisfiable checkSat() or checkSatAssuming()
   * query.
   */
  public boolean isSat()
  {
    return isSat(getPointer());
  }

  private boolean isSat(long pointer)
  {
    return pointer != 0 && CApi.cvc5_result_is_sat(pointer);
  }

  /**
   * Determine if if query was an unsatisfiable checkSat() or
   * checkSatAssuming() query.
   *
   * @return True if query was an unsatisfiable checkSat() or
   * checkSatAssuming() query.
   */
  public boolean isUnsat()
  {
    return isUnsat(getPointer());
  }

  private boolean isUnsat(long pointer)
  {
    return pointer != 0 && CApi.cvc5_result_is_unsat(pointer);
  }

  /**
   * Determine if query was a checkSat() or checkSatAssuming() query and
   * cvc5 was not able to determine (un)satisfiability.
   *
   * @return True if query was a checkSat() or checkSatAssuming() query and
   * cvc5 was not able to determine (un)satisfiability.
   */
  public boolean isUnknown()
  {
    return isUnknown(getPointer());
  }

  private boolean isUnknown(long pointer)
  {
    return pointer != 0 && CApi.cvc5_result_is_unknown(pointer);
  }

  /**
   * Operator overloading for equality of two results.
   * @param r The result to compare to for equality.
   * @return True if the results are equal.
   */
  @Override
  public boolean equals(Object r)
  {
    if (this == r)
    {
      return true;
    }
    if (r == null || getClass() != r.getClass())
    {
      return false;
    }
    Result result = (Result) r;
    if (this.pointer == result.pointer)
    {
      return true;
    }
    return equals(getPointer(), result.getPointer());
  }

  private boolean equals(long pointer1, long pointer2)
  {
    if (pointer1 == 0 || pointer2 == 0)
    {
      // A null result is equal to the results without a status.
      return isNull(pointer1) && isNull(pointer2);
    }
    return CApi.cvc5_result_is_equal(pointer1, pointer2);
  }

  /**
   * Get an explanation for an unknown query result.
   * @return The explanation.
   */
  public UnknownExplanation getUnknownExplanation()
  {
    try
    {
      int explanation = getUnknownExplanation(getPointer());
      return UnknownExplanation.fromInt(explanation);
    }
    catch (CVC5ApiException e)
    {
      e.printStackTrace();
      throw new RuntimeException(e.getMessage());
    }
  }

  private int getUnknownExplanation(long pointer)
  {
    if (pointer == 0)
    {
      // The C API rejects null results, which have no explanation.
      return UnknownExplanation.UNKNOWN_REASON.getValue();
    }
    return CApi.cvc5_result_get_unknown_explanation(pointer);
  }

  /**
   * @return A string representation of this result.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      // The C API rejects null results.
      return "none";
    }
    return Native.string(CApi.cvc5_result_to_string(pointer));
  }

  /**
   * Get the hash value of a result.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(getPointer()));
  }

  private long hashCode(long pointer)
  {
    if (pointer == 0)
    {
      // The C API rejects null results. The C++ API hashes the string
      // representation of a result; any fixed value is consistent with equals.
      return toString(pointer).hashCode();
    }
    return CApi.cvc5_result_hash(pointer);
  }
}
