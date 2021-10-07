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

/** Has the current and the default value */
public abstract class ValueInfo<T> extends VariantInfo
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