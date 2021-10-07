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

import java.math.BigInteger;

/**
 * Holds some description about a particular option, including its name, its
 * aliases, whether the option was explicitly set by the user, and information
 * concerning its value. The `valueInfo` member holds any of the following
 * alternatives:
 * - VoidInfo if the option holds no value (or the value has no native type)
 * - ValueInfo if the option is of type boolean or String, holds the
 *   current value and the default value.
 * - NumberInfo if the option is of type BigInteger or double, holds
 *   the current and default value, as well as the minimum and maximum.
 * - ModeInfo if the option is a mode option, holds the current and default
 *   values, as well as a list of valid modes.
 * Additionally, this class provides convenience functions to obtain the
 * current value of an option in a type-safe manner using boolValue(),
 * stringValue(), intValue(), and doubleValue(). They assert that
 * the option has the respective type and return the current value.
 */
public class OptionInfo extends AbstractPointer
{
  // region construction and destruction
  OptionInfo(Solver solver, long pointer)
  {
    super(solver, pointer);
    this.name = getName(pointer);
    this.aliases = getAliases(pointer);
    this.setByUser = getSetByUser(pointer);
    this.variantInfo = getVariantInfo(pointer);
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

  private native String getName(long pointer);

  private native String[] getAliases(long pointer);

  private native boolean getSetByUser(long pointer);

  private native VariantInfo getVariantInfo(long pointer);

  /** The option name */
  private final String name;
  public String getName()
  {
    return name;
  }
  /** The option name aliases */
  private final String[] aliases;
  public String[] getAliases()
  {
    return aliases;
  }
  /** Whether the option was explicitly set by the user */
  private final boolean setByUser;
  public boolean getSetByUser()
  {
    return setByUser;
  }

  /** The option variant information */
  private final VariantInfo variantInfo;
  public VariantInfo getVariantInfo()
  {
    return variantInfo;
  }

  /**
   * Obtain the current value as a boolean. Asserts that valueInfo holds a boolean.
   */
  public boolean booleanValue()
  {
    return booleanValue(pointer);
  }

  private native boolean booleanValue(long pointer);

  /**
   * Obtain the current value as a string. Asserts that valueInfo holds a
   * string.
   */
  public String stringValue()
  {
    return stringValue(pointer);
  }

  private native String stringValue(long pointer);

  /**
   * Obtain the current value as as int. Asserts that valueInfo holds an int.
   */
  public BigInteger intValue()
  {
    return intValue(pointer);
  }

  private native BigInteger intValue(long pointer);

  /**
   * Obtain the current value as a double. Asserts that valueInfo holds a
   * double.
   */
  public double doubleValue()
  {
    return doubleValue(pointer);
  }

  private native double doubleValue(long pointer);
};
