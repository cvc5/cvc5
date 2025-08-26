/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
    super(getNullSynthResult());
  }

  private static native long getNullSynthResult();

  SynthResult(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

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
    return equals(pointer, result.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Determine if SynthResult is empty, i.e., a nullary SynthResult, and not
   * an actual result returned from a synthesis query.
   *
   * @return True if SynthResult is empty, i.e., a nullary SynthResult, and not
   * an actual result returned from a synthesis query.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Determine if the synthesis query has a solution.
   *
   * @return True if the synthesis query has a solution.
   */
  public boolean hasSolution()
  {
    return hasSolution(pointer);
  }

  private native boolean hasSolution(long pointer);

  /**
   * Determine if the synthesis query has no solution.
   *
   * @return True if the synthesis query has no solution. In this case, it was
   * determined there was no solution.
   */
  public boolean hasNoSolution()
  {
    return hasNoSolution(pointer);
  }

  private native boolean hasNoSolution(long pointer);

  /**
   * Determine if the result of the synthesis query could not be determined.
   *
   * @return True if the result of the synthesis query could not be determined.
   */
  public boolean isUnknown()
  {
    return isUnknown(pointer);
  }

  private native boolean isUnknown(long pointer);

  /**
   * @return A string representation of this result.
   */
  protected native String toString(long pointer);

  /**
   * Get the hash value of a synthesis result.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return hashCode(pointer);
  }

  private native int hashCode(long pointer);
}
