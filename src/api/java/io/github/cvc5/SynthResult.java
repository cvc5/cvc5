/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

  public long getPointer()
  {
    return pointer;
  }

  /**
   * @return True if SynthResult is empty, i.e., a nullary SynthResult, and not
   * an actual result returned from a synthesis query.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return True if the synthesis query has a solution.
   */
  public boolean hasSolution()
  {
    return hasSolution(pointer);
  }

  private native boolean hasSolution(long pointer);

  /**
   * @return True if the synthesis query has no solution. In this case, it was
   * determined there was no solution.
   */
  public boolean hasNoSolution()
  {
    return hasNoSolution(pointer);
  }

  private native boolean hasNoSolution(long pointer);

  /**
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
}
