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

import io.github.cvc5.capi.CApi;
import io.github.cvc5.capi.Cvc5OptionInfo;
import io.github.cvc5.modes.OptionCategory;
import java.lang.foreign.MemorySegment;
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

  /**
   * Construct from the information about an option filled in by
   * {@code cvc5_get_option_info()}, see {@link Solver#getOptionInfo(String)}.
   *
   * <p>The information is only valid until the next call to
   * {@code cvc5_get_option_info()} on this thread, so it is copied right away.
   * The object thus owns no native object (its pointer is 0).</p>
   *
   * @param ctx The context of the solver (unused).
   * @param info A {@code Cvc5OptionInfo} struct filled in by
   *             {@code cvc5_get_option_info()}, which must remain valid
   *             during this call.
   */
  OptionInfo(NativeContext ctx, MemorySegment info)
  {
    super(ctx, MemorySegment.NULL, null);
    info = info.reinterpret(Cvc5OptionInfo.sizeof());
    this.name = Native.copyString(Cvc5OptionInfo.name(info));
    this.aliases = Native.strings(Cvc5OptionInfo.aliases(info), Cvc5OptionInfo.num_aliases(info));
    this.setByUser = Cvc5OptionInfo.is_set_by_user(info);
    try
    {
      this.category = OptionCategory.fromInt(Cvc5OptionInfo.category(info));
    }
    catch (CVC5ApiException e)
    {
      throw new RuntimeException("Invalid OptionCategory value", e);
    }
    this.kind = Cvc5OptionInfo.kind(info);
    this.baseInfo = getBaseInfo(info);
    this.str = Native.string(CApi.cvc5_option_info_to_string(info));
  }

  public String toString()
  {
    return str;
  }

  /**
   * @return A string representation of this OptionInfo.
   */
  protected String toString(long pointer)
  {
    return str;
  }

  // endregion

  // region reading struct Cvc5OptionInfo of the C API

  /** Values of {@code Cvc5OptionInfoKind}. */
  private static final int KIND_VOID = 0;
  private static final int KIND_BOOL = 1;
  private static final int KIND_STR = 2;
  private static final int KIND_INT64 = 3;
  private static final int KIND_UINT64 = 4;
  private static final int KIND_DOUBLE = 5;
  private static final int KIND_MODES = 6;

  /**
   * Convert a {@code uint64_t} value to a {@code BigInteger}.
   *
   * @param value The value, as the same bits in a {@code long}.
   * @return The value.
   */
  private static BigInteger unsigned(long value)
  {
    return new BigInteger(Long.toUnsignedString(value));
  }

  // endregion

  /** Abstract class for OptionInfo values */
  public abstract class BaseInfo
  {
    /**
     * Construct a new BaseInfo.
     */
    public BaseInfo() {}
  }

  /**
   * Has the current and the default value
   *
   * @param <T> the type of the value
   */
  public class ValueInfo<T> extends BaseInfo
  {
    private final T defaultValue;
    private final T currentValue;

    /**
     * Construct a new {@code ValueInfo} instance with the given default and current values.
     *
     * @param defaultValue The default value.
     * @param currentValue The current value.
     */
    public ValueInfo(T defaultValue, T currentValue)
    {
      this.defaultValue = defaultValue;
      this.currentValue = currentValue;
    }
    /**
     * Get the default value.
     *
     * @return The default value.
     */
    public T getDefaultValue()
    {
      return defaultValue;
    }
    /**
     * Get the current value.
     *
     * @return The current value.
     */
    public T getCurrentValue()
    {
      return currentValue;
    }
  }

  /**
   * Information for mode option values.
   */
  public class ModeInfo extends ValueInfo<String>
  {
    private final String[] modes;

    /**
     * Constructs a {@code ModeInfo} instance with the specified default value,
     * current value, and available mode options.
     *
     * @param defaultValue The default value.
     * @param currentValue The current value.
     * @param modes The possible mode values.
     */
    public ModeInfo(String defaultValue, String currentValue, String[] modes)
    {
      super(defaultValue, currentValue);
      this.modes = modes;
    }

    /**
     * Get the list of valid mode values.
     *
     * @return An array of available mode options.
     */
    public String[] getModes()
    {
      return modes;
    }
  }

  /** Has no value information */
  public class VoidInfo extends BaseInfo
  {
    /**
     * Construct a new VoidInfo.
     */
    public VoidInfo() {}
  }

  /**
   * Default value, current value, minimum and maximum of a numeric value
   *
   * @param <T> the type of the numeric value
   */
  public class NumberInfo<T> extends ValueInfo<T>
  {
    private final T minimum;
    private final T maximum;

    /**
     * Construct a {@code NumberInfo} instance with specified default value,
     * current value, minimum, and maximum.
     *
     * @param defaultValue The default value.
     * @param currentValue The current value.
     * @param minimum The minimum value.
     * @param maximum The maximum value.
     */
    public NumberInfo(T defaultValue, T currentValue, T minimum, T maximum)
    {
      super(defaultValue, currentValue);
      this.minimum = minimum;
      this.maximum = maximum;
    }

    /**
     * Get the minimum value.
     *
     * @return The minimum value.
     */
    public T getMinimum()
    {
      return minimum;
    }

    /**
     * Get the maximum value.
     *
     * @return The maximum value.
     */
    public T getMaximum()
    {
      return maximum;
    }
  }

  /**
   * Get the value information of an option.
   *
   * @param info The {@code Cvc5OptionInfo} struct.
   * @return The value information.
   */
  private BaseInfo getBaseInfo(MemorySegment info)
  {
    switch (kind)
    {
      case KIND_BOOL:
      {
        MemorySegment b = Cvc5OptionInfo.info_bool(info);
        return new ValueInfo<Boolean>(
            Cvc5OptionInfo.BoolInfo.dflt(b), Cvc5OptionInfo.BoolInfo.cur(b));
      }
      case KIND_STR:
      {
        MemorySegment s = Cvc5OptionInfo.info_str(info);
        return new ValueInfo<String>(Native.copyString(Cvc5OptionInfo.StringInfo.dflt(s)),
            Native.copyString(Cvc5OptionInfo.StringInfo.cur(s)));
      }
      case KIND_INT64:
      {
        MemorySegment num = Cvc5OptionInfo.info_int(info);
        return new NumberInfo<BigInteger>(BigInteger.valueOf(Cvc5OptionInfo.IntInfo.dflt(num)),
            BigInteger.valueOf(Cvc5OptionInfo.IntInfo.cur(num)),
            Cvc5OptionInfo.IntInfo.has_min(num)
                ? BigInteger.valueOf(Cvc5OptionInfo.IntInfo.min(num))
                : null,
            Cvc5OptionInfo.IntInfo.has_max(num)
                ? BigInteger.valueOf(Cvc5OptionInfo.IntInfo.max(num))
                : null);
      }
      case KIND_UINT64:
      {
        MemorySegment num = Cvc5OptionInfo.info_uint(info);
        return new NumberInfo<BigInteger>(unsigned(Cvc5OptionInfo.UIntInfo.dflt(num)),
            unsigned(Cvc5OptionInfo.UIntInfo.cur(num)),
            Cvc5OptionInfo.UIntInfo.has_min(num) ? unsigned(Cvc5OptionInfo.UIntInfo.min(num))
                                                 : null,
            Cvc5OptionInfo.UIntInfo.has_max(num) ? unsigned(Cvc5OptionInfo.UIntInfo.max(num))
                                                 : null);
      }
      case KIND_DOUBLE:
      {
        MemorySegment num = Cvc5OptionInfo.info_double(info);
        return new NumberInfo<Double>(Cvc5OptionInfo.DoubleInfo.dflt(num),
            Cvc5OptionInfo.DoubleInfo.cur(num),
            Cvc5OptionInfo.DoubleInfo.has_min(num) ? Cvc5OptionInfo.DoubleInfo.min(num) : null,
            Cvc5OptionInfo.DoubleInfo.has_max(num) ? Cvc5OptionInfo.DoubleInfo.max(num) : null);
      }
      case KIND_MODES:
      {
        MemorySegment mode = Cvc5OptionInfo.info_mode(info);
        return new ModeInfo(Native.copyString(Cvc5OptionInfo.ModeInfo.dflt(mode)),
            Native.copyString(Cvc5OptionInfo.ModeInfo.cur(mode)),
            Native.strings(
                Cvc5OptionInfo.ModeInfo.modes(mode), Cvc5OptionInfo.ModeInfo.num_modes(mode)));
      }
      default: return new VoidInfo();
    }
  }

  /** The kind of the value information ({@code Cvc5OptionInfoKind}) */
  private final int kind;

  /** The string representation */
  private final String str;

  /** The option name */
  private final String name;

  /**
   * Get the name of the option.
   *
   * @return The option name.
   */
  public String getName()
  {
    return name;
  }

  /** The option name aliases */
  private final String[] aliases;
  /**
   * Get the option name aliases.
   *
   * @return An array of alias strings associated with the option.
   */
  public String[] getAliases()
  {
    return aliases;
  }

  /** Whether the option was explicitly set by the user */
  private final boolean setByUser;

  /**
   * Determine if the option was set by the user.
   *
   * @return True if the option was set by the user.
   */
  public boolean getSetByUser()
  {
    return setByUser;
  }

  /** The option variant information */
  private final BaseInfo baseInfo;
  /**
   * Get base info.
   *
   * @return The base info.
   */
  public BaseInfo getBaseInfo()
  {
    return baseInfo;
  }

  /**
   * Obtain the current value as a Boolean.
   * Asserts that valueInfo holds a Boolean.
   * @return The Boolean value.
   */
  public boolean booleanValue()
  {
    if (kind != KIND_BOOL)
    {
      throw new CVC5ApiRecoverableException(name + " is not a bool option");
    }
    return (Boolean) ((ValueInfo<?>) baseInfo).getCurrentValue();
  }

  /**
   * Obtain the current value as a string.
   * Asserts that valueInfo holds a string.
   * @return The string value.
   */
  public String stringValue()
  {
    if (kind != KIND_STR)
    {
      throw new CVC5ApiRecoverableException(name + " is not a string option");
    }
    return (String) ((ValueInfo<?>) baseInfo).getCurrentValue();
  }

  /**
   * Obtain the current value as as int.
   * Asserts that valueInfo holds an int.
   * @return The integer value.
   */
  public BigInteger intValue()
  {
    if (kind != KIND_INT64 && kind != KIND_UINT64)
    {
      throw new CVC5ApiRecoverableException("Option is neither int64_t nor uint64_t");
    }
    return (BigInteger) ((ValueInfo<?>) baseInfo).getCurrentValue();
  }

  /**
   * Obtain the current value as a double.
   * Asserts that valueInfo holds a double.
   * @return The double value.
   */
  public double doubleValue()
  {
    if (kind != KIND_DOUBLE)
    {
      throw new CVC5ApiRecoverableException(name + " is not a double option");
    }
    return (Double) ((ValueInfo<?>) baseInfo).getCurrentValue();
  }

  /** The option category */
  private final OptionCategory category;

  /**
   * Get the category of the option.
   *
   * @return The option category.
   */
  public OptionCategory getCategory()
  {
    return category;
  }
}
