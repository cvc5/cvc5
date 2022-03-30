/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Abdalrhman Mohamed, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5.api;

import java.util.HashMap;
import java.util.Map;

public class Result extends AbstractPointer
{
  // region construction and destruction
  Result(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /**
   * @return true if Result is empty, i.e., a nullary Result, and not an actual
   * result returned from a checkSat() (and friends) query.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return true if query was a satisfiable checkSat() or checkSatAssuming()
   * query.
   */
  public boolean isSat()
  {
    return isSat(pointer);
  }

  private native boolean isSat(long pointer);

  /**
   * @return true if query was an unsatisfiable checkSat() or
   * checkSatAssuming() query.
   */
  public boolean isUnsat()
  {
    return isUnsat(pointer);
  }

  private native boolean isUnsat(long pointer);

  /**
   * @return true if query was a checkSat() or checkSatAssuming() query and
   * cvc5 was not able to determine (un)satisfiability.
   */
  public boolean isUnknown()
  {
    return isUnknown(pointer);
  }

  private native boolean isUnknown(long pointer);

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
    Result result = (Result) r;
    if (this.pointer == result.pointer)
    {
      return true;
    }
    return equals(pointer, result.getPointer());
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
    catch (CVC5ApiException e)
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
