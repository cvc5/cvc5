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
 * Encapsulation of a solver OMT result.
 *
 * This is the return value of the API methods:
 *   - Solver::optimizeSat()
 *   - Solver::optimizeSatNext()
 *
 * which we call optimization queries.  This class indicates whether the
 * optimization query returned an optimal solution, a non-optimal (approximate) solution, 
 * has no solution, or is unknown.
 */
public class OmtResult extends AbstractPointer
{
  /**
   * Null OmtResult
   */
  public OmtResult()
  {
    super(getNullOmtResult());
  }

  private static native long getNullOmtResult();

  OmtResult(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  /**
   * Operator overloading for equality of two OMT results.
   * @param r The OMT result to compare to for equality.
   * @return True if the OMT results are equal.
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
    OmtResult result = (OmtResult) r;
    if (this.pointer == result.pointer)
    {
      return true;
    }
    return equals(pointer, result.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * @return True if OmtResult is empty, i.e., a nullary OmtResult, and not
   * an actual result returned from an optimization query.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return True if the OMT query has an optimal solution.
   */
  public boolean isOptimal()
  {
    return isOptimal(pointer);
  }

  private native boolean isOptimal(long pointer);

  /** @return True if the query has a limit-optimal solution. */
  public boolean isLimitOptimal()
  {
    return isLimitOptimal(pointer);
  }

  private native boolean isLimitOptimal(long pointer);

  /** @return True if the query returned a non-optimal (approximate) result. */
  public boolean isNonOptimal()
  {
    return isNonOptimal(pointer);
  }

  private native boolean isNonOptimal(long pointer);

  /** @return True if the query is unbounded. */
  public boolean isUnbounded()
  {
    return isUnbounded(pointer);
  }

  private native boolean isUnbounded(long pointer);

  /** @return True if the query is unsatisfiable. */
  public boolean isUnsat()
  {
    return isUnsat(pointer);
  }

  private native boolean isUnsat(long pointer);

  /** @return True if the outcome is unknown. */
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
