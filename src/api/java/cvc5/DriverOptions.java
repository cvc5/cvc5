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

import java.util.Optional;

/**
 * Holds some description about a particular option, including its name, its
 * aliases, whether the option was explicitly set by the user, and information
 * concerning its value. The `valueInfo` member holds any of the following
 * alternatives:
 * - VoidInfo if the option holds no value (or the value has no native type)
 * - ValueInfo<T> if the option is of type boolean or String, holds the
 *   current value and the default value.
 * - NumberInfo<T> if the option is of type BigInteger or double, holds
 *   the current and default value, as well as the minimum and maximum.
 * - ModeInfo if the option is a mode option, holds the current and default
 *   values, as well as a list of valid modes.
 * Additionally, this class provides convenience functions to obtain the
 * current value of an option in a type-safe manner using boolValue(),
 * stringValue(), intValue(), and doubleValue(). They assert that
 * the option has the respective type and return the current value.
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
  protected native String toString(long pointer);

  // endregion
};
