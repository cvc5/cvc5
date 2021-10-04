/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mudathir Mohamed
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

package cvc5;

/**
 * Provides access to options that can not be communicated via the regular
 * getOption() or getOptionInfo() methods. This class does not store the options
 * itself, but only acts as a wrapper to the solver object. It can thus no
 * longer be used after the solver object has been destroyed.
 */
public class DriverOptions extends AbstractPointer
{
  // region construction and destruction
  DriverOptions(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  @Override public void finalize()
  {
    deletePointer(pointer);
  }

  /**
   * @return a string representation of this optionInfo.
   */
  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException();
  }

  // endregion
};
