/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Gereon Kremer
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

import java.math.BigInteger;

/**
 * Holds some description about a particular option, including its name, its
 * aliases, whether the option was explicitly set by the user, and information
 * concerning its value. The {@code valueInfo} member holds any of the following
 * alternatives:
 * <ul>
 *   <li>
 *     {@link OptionInfo.VoidInfo} if the option holds no value (or the value
 *     has no native type)
 *   </li>
 *   <li>
 *     {@link OptionInfo.ValueInfo} if the option is of type boolean or String,
 *     holds the current value and the default value.
 *   </li>
 *   <li>
 *     {@link OptionInfo.NumberInfo} if the option is of type BigInteger or
 *     double, holds the current and default value, as well as the minimum and
 *     maximum.
 *   </li>
 *   <li>
 *     {@link OptionInfo.ModeInfo} if the option is a mode option, holds the
 *     current and default values, as well as a list of valid modes.
 *   </li>
 * </ul>
 *
 * Additionally, this class provides convenience functions to obtain the
 * current value of an option in a type-safe manner using
 * {@link OptionInfo#booleanValue()}, {@link OptionInfo#stringValue()},
 * {@link OptionInfo#intValue()}, and {@link OptionInfo#doubleValue()}.
 * They assert that the option has the respective type and return the current
 * value.
 */
public class OptionInfo extends AbstractPointer
{
  // region construction and destruction
  OptionInfo(long pointer)
  {
    super(pointer);
    this.name = getName(pointer);
    this.aliases = getAliases(pointer);
    this.setByUser = getSetByUser(pointer);
    this.baseInfo = getBaseInfo(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  public String toString()
  {
    return toString(pointer);
  }

  /**
   * @return A string representation of this OptionInfo.
   */
  protected native String toString(long pointer);

  // endregion

  /** Abstract class for OptionInfo values */
  public abstract class BaseInfo
  {
  }

  /** Has the current and the default value */
  public class ValueInfo<T> extends BaseInfo
  {
    private final T defaultValue;
    private final T currentValue;
    public ValueInfo(T defaultValue, T currentValue)
    {
      this.defaultValue = defaultValue;
      this.currentValue = currentValue;
    }
    public T getDefaultValue()
    {
      return defaultValue;
    }
    public T getCurrentValue()
    {
      return currentValue;
    }
  }

  public class ModeInfo extends ValueInfo<String>
  {
    private final String[] modes;

    public ModeInfo(String defaultValue, String currentValue, String[] modes)
    {
      super(defaultValue, currentValue);
      this.modes = modes;
    }
    public String[] getModes()
    {
      return modes;
    }
  }

  /** Has no value information */
  public class VoidInfo extends BaseInfo
  {
  }

  /** Default value, current value, minimum and maximum of a numeric value */
  public class NumberInfo<T> extends ValueInfo<T>
  {
    private final T minimum;
    private final T maximum;
    public NumberInfo(T defaultValue, T currentValue, T minimum, T maximum)
    {
      super(defaultValue, currentValue);
      this.minimum = minimum;
      this.maximum = maximum;
    }
    public T getMinimum()
    {
      return minimum;
    }
    public T getMaximum()
    {
      return maximum;
    }
  }

  private native String getName(long pointer);

  private native String[] getAliases(long pointer);

  private native boolean getSetByUser(long pointer);

  private native BaseInfo getBaseInfo(long pointer);

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
  private final BaseInfo baseInfo;
  public BaseInfo getBaseInfo()
  {
    return baseInfo;
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
}
