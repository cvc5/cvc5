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

/**
 * Encapsulation of a solver synth result.
 *
 * This is the return value of the API methods:
 *   - {@link Solver#checkSynth()}
 *   - {@link Solver#checkSynthNext()}
 *
 * which we call synthesis queries.  This class indicates whether the
 * synthesis query has a solution, has no solution, or is unknown.
 */
public class SynthResult extends AbstractPointer
{
  /**
   * Null synthResult
   */
  public SynthResult()
  {
    super(null, 0, null);
  }

  SynthResult(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, SynthResult::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_synth_result_release(pointer);
  }

  /**
   * Operator overloading for equality of two synthesis results.
   * @param r The synthesis result to compare to for equality.
   * @return True if the synthesis results are equal.
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
    SynthResult result = (SynthResult) r;
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
      // A null synthesis result is equal to the synthesis results without a
      // status.
      return isNull(pointer1) && isNull(pointer2);
    }
    return CApi.cvc5_synth_result_is_equal(pointer1, pointer2);
  }

  /**
   * Determine if SynthResult is empty, i.e., a nullary SynthResult, and not
   * an actual result returned from a synthesis query.
   *
   * @return True if SynthResult is empty, i.e., a nullary SynthResult, and not
   * an actual result returned from a synthesis query.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private boolean isNull(long pointer)
  {
    return pointer == 0 || CApi.cvc5_synth_result_is_null(pointer);
  }

  /**
   * Determine if the synthesis query has a solution.
   *
   * @return True if the synthesis query has a solution.
   */
  public boolean hasSolution()
  {
    return hasSolution(getPointer());
  }

  private boolean hasSolution(long pointer)
  {
    return pointer != 0 && CApi.cvc5_synth_result_has_solution(pointer);
  }

  /**
   * Determine if the synthesis query has no solution.
   *
   * @return True if the synthesis query has no solution. In this case, it was
   * determined there was no solution.
   */
  public boolean hasNoSolution()
  {
    return hasNoSolution(getPointer());
  }

  private boolean hasNoSolution(long pointer)
  {
    return pointer != 0 && CApi.cvc5_synth_result_has_no_solution(pointer);
  }

  /**
   * Determine if the result of the synthesis query could not be determined.
   *
   * @return True if the result of the synthesis query could not be determined.
   */
  public boolean isUnknown()
  {
    return isUnknown(getPointer());
  }

  private boolean isUnknown(long pointer)
  {
    return pointer != 0 && CApi.cvc5_synth_result_is_unknown(pointer);
  }

  /**
   * @return A string representation of this result.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      // The C API rejects null synthesis results.
      return "(NONE)";
    }
    return Native.string(CApi.cvc5_synth_result_to_string(pointer));
  }

  /**
   * Get the hash value of a synthesis result.
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
      // The C API rejects null synthesis results. The C++ API hashes the string
      // representation of a synthesis result; any fixed value is consistent
      // with equals.
      return toString(pointer).hashCode();
    }
    return CApi.cvc5_synth_result_hash(pointer);
  }
}
