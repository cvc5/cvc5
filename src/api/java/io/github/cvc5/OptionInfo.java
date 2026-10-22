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

import static java.lang.foreign.ValueLayout.ADDRESS;
import static java.lang.foreign.ValueLayout.JAVA_BOOLEAN;
import static java.lang.foreign.ValueLayout.JAVA_DOUBLE;
import static java.lang.foreign.ValueLayout.JAVA_INT;
import static java.lang.foreign.ValueLayout.JAVA_LONG;

import io.github.cvc5.modes.OptionCategory;
import java.lang.foreign.MemoryLayout;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.StructLayout;
import java.lang.foreign.ValueLayout;
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
   * @param pointer The address of a {@code Cvc5OptionInfo} struct filled in
   *                by {@code cvc5_get_option_info()}, which must remain
   *                valid during this call.
   */
  OptionInfo(NativeContext ctx, long pointer)
  {
    super(ctx, 0, null);
    MemorySegment info = MemorySegment.ofAddress(pointer).reinterpret(LAYOUT.byteSize());
    this.name = Native.string(address(info, NAME));
    this.aliases = Native.strings(address(info, ALIASES), info.get(JAVA_LONG, NUM_ALIASES));
    this.setByUser = info.get(JAVA_BOOLEAN, IS_SET_BY_USER);
    try
    {
      this.category = OptionCategory.fromInt(info.get(JAVA_INT, CATEGORY));
    }
    catch (CVC5ApiException e)
    {
      throw new RuntimeException("Invalid OptionCategory value", e);
    }
    this.kind = info.get(JAVA_INT, KIND);
    this.baseInfo = getBaseInfo(info);
    this.str = Native.string(CApi.cvc5_option_info_to_string(pointer));
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

  // region layout of struct Cvc5OptionInfo of the C API

  /**
   * The layout of {@code struct IntInfo}, {@code struct UIntInfo} and
   * {@code struct DoubleInfo} in {@code struct Cvc5OptionInfo}.
   *
   * @param value The layout of the values.
   * @return The layout.
   */
  private static StructLayout numberInfoLayout(ValueLayout value)
  {
    return MemoryLayout.structLayout(value.withName("dflt"),
        value.withName("cur"),
        value.withName("min"),
        value.withName("max"),
        JAVA_BOOLEAN.withName("has_min"),
        JAVA_BOOLEAN.withName("has_max"),
        MemoryLayout.paddingLayout(6));
  }

  /** The layout of {@code struct Cvc5OptionInfo}. */
  private static final StructLayout LAYOUT =
      MemoryLayout.structLayout(JAVA_INT.withName("kind"), // Cvc5OptionInfoKind
          MemoryLayout.paddingLayout(4),
          ADDRESS.withName("name"),
          JAVA_LONG.withName("num_aliases"), // size_t
          ADDRESS.withName("aliases"),
          JAVA_LONG.withName("num_no_supports"), // size_t
          ADDRESS.withName("no_supports"),
          JAVA_BOOLEAN.withName("is_set_by_user"),
          JAVA_BOOLEAN.withName("is_expert"),
          JAVA_BOOLEAN.withName("is_regular"),
          MemoryLayout.paddingLayout(1),
          JAVA_INT.withName("category"), // Cvc5OptionCategory
          MemoryLayout.structLayout(JAVA_BOOLEAN.withName("dflt"), JAVA_BOOLEAN.withName("cur"))
              .withName("info_bool"),
          MemoryLayout.paddingLayout(6),
          MemoryLayout.structLayout(ADDRESS.withName("dflt"), ADDRESS.withName("cur"))
              .withName("info_str"),
          numberInfoLayout(JAVA_LONG).withName("info_int"), // int64_t
          numberInfoLayout(JAVA_LONG).withName("info_uint"), // uint64_t
          numberInfoLayout(JAVA_DOUBLE).withName("info_double"),
          MemoryLayout
              .structLayout(ADDRESS.withName("dflt"),
                  ADDRESS.withName("cur"),
                  JAVA_LONG.withName("num_modes"), // size_t
                  ADDRESS.withName("modes"))
              .withName("info_mode"),
          ADDRESS.withName("d_cpp_info"));

  /**
   * Get the offset of a field of {@code struct Cvc5OptionInfo}.
   *
   * @param path The names of the field and of the structs containing it.
   * @return The offset in bytes.
   */
  private static long offset(String... path)
  {
    MemoryLayout.PathElement[] elements = new MemoryLayout.PathElement[path.length];
    for (int i = 0; i < path.length; i++)
    {
      elements[i] = MemoryLayout.PathElement.groupElement(path[i]);
    }
    return LAYOUT.byteOffset(elements);
  }

  private static final long KIND = offset("kind");
  private static final long NAME = offset("name");
  private static final long NUM_ALIASES = offset("num_aliases");
  private static final long ALIASES = offset("aliases");
  private static final long IS_SET_BY_USER = offset("is_set_by_user");
  private static final long CATEGORY = offset("category");
  private static final long BOOL_DFLT = offset("info_bool", "dflt");
  private static final long BOOL_CUR = offset("info_bool", "cur");
  private static final long STR_DFLT = offset("info_str", "dflt");
  private static final long STR_CUR = offset("info_str", "cur");
  private static final long INT_INFO = offset("info_int");
  private static final long UINT_INFO = offset("info_uint");
  private static final long DOUBLE_INFO = offset("info_double");
  // offsets in struct IntInfo, UIntInfo and DoubleInfo
  private static final long NUM_DFLT = offset("info_int", "dflt") - INT_INFO;
  private static final long NUM_CUR = offset("info_int", "cur") - INT_INFO;
  private static final long NUM_MIN = offset("info_int", "min") - INT_INFO;
  private static final long NUM_MAX = offset("info_int", "max") - INT_INFO;
  private static final long NUM_HAS_MIN = offset("info_int", "has_min") - INT_INFO;
  private static final long NUM_HAS_MAX = offset("info_int", "has_max") - INT_INFO;
  private static final long MODE_DFLT = offset("info_mode", "dflt");
  private static final long MODE_CUR = offset("info_mode", "cur");
  private static final long MODE_NUM_MODES = offset("info_mode", "num_modes");
  private static final long MODE_MODES = offset("info_mode", "modes");

  /** Values of {@code Cvc5OptionInfoKind}. */
  private static final int KIND_VOID = 0;
  private static final int KIND_BOOL = 1;
  private static final int KIND_STR = 2;
  private static final int KIND_INT64 = 3;
  private static final int KIND_UINT64 = 4;
  private static final int KIND_DOUBLE = 5;
  private static final int KIND_MODES = 6;

  /**
   * Read a pointer.
   *
   * @param segment The memory to read from.
   * @param offset The offset of the pointer.
   * @return The pointer.
   */
  private static long address(MemorySegment segment, long offset)
  {
    return segment.get(ADDRESS, offset).address();
  }

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
        return new ValueInfo<Boolean>(
            info.get(JAVA_BOOLEAN, BOOL_DFLT), info.get(JAVA_BOOLEAN, BOOL_CUR));
      case KIND_STR:
        return new ValueInfo<String>(
            Native.string(address(info, STR_DFLT)), Native.string(address(info, STR_CUR)));
      case KIND_INT64:
      {
        MemorySegment num = info.asSlice(INT_INFO);
        return new NumberInfo<BigInteger>(BigInteger.valueOf(num.get(JAVA_LONG, NUM_DFLT)),
            BigInteger.valueOf(num.get(JAVA_LONG, NUM_CUR)),
            num.get(JAVA_BOOLEAN, NUM_HAS_MIN) ? BigInteger.valueOf(num.get(JAVA_LONG, NUM_MIN))
                                               : null,
            num.get(JAVA_BOOLEAN, NUM_HAS_MAX) ? BigInteger.valueOf(num.get(JAVA_LONG, NUM_MAX))
                                               : null);
      }
      case KIND_UINT64:
      {
        MemorySegment num = info.asSlice(UINT_INFO);
        return new NumberInfo<BigInteger>(unsigned(num.get(JAVA_LONG, NUM_DFLT)),
            unsigned(num.get(JAVA_LONG, NUM_CUR)),
            num.get(JAVA_BOOLEAN, NUM_HAS_MIN) ? unsigned(num.get(JAVA_LONG, NUM_MIN)) : null,
            num.get(JAVA_BOOLEAN, NUM_HAS_MAX) ? unsigned(num.get(JAVA_LONG, NUM_MAX)) : null);
      }
      case KIND_DOUBLE:
      {
        MemorySegment num = info.asSlice(DOUBLE_INFO);
        return new NumberInfo<Double>(num.get(JAVA_DOUBLE, NUM_DFLT),
            num.get(JAVA_DOUBLE, NUM_CUR),
            num.get(JAVA_BOOLEAN, NUM_HAS_MIN) ? num.get(JAVA_DOUBLE, NUM_MIN) : null,
            num.get(JAVA_BOOLEAN, NUM_HAS_MAX) ? num.get(JAVA_DOUBLE, NUM_MAX) : null);
      }
      case KIND_MODES:
        return new ModeInfo(Native.string(address(info, MODE_DFLT)),
            Native.string(address(info, MODE_CUR)),
            Native.strings(address(info, MODE_MODES), info.get(JAVA_LONG, MODE_NUM_MODES)));
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
