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

/**
 * A cvc5 Weight. Used for assigning weights to rules in a Sygus grammar.
 */
public class Weight extends AbstractPointer
{
  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package.
   *
   * @param pointer the cpp pointer to Weight
   */
  Weight(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException("Weight.toString() is not supported in the cpp api");
  }

  /**
   * Get the name of this weight attribute.
   *
   * @return The name of this weight attribute.
   */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

  /**
   * Get the default value of this weight attribute.
   *
   * @return The default value of this weight attribute.
   */
  public Term getDefaultValue()
  {
    return new Term(getDefaultValue(pointer));
  }

  private native long getDefaultValue(long pointer);

  /**
   * Equality operator.
   *
   * @param t The weight to compare to for equality.
   * @return True if the weights are equal.
   */
  @Override
  public boolean equals(Object t)
  {
    if (this == t)
    {
      return true;
    }
    if (t == null || getClass() != t.getClass())
    {
      return false;
    }
    Weight weight = (Weight) t;
    if (pointer == weight.pointer)
    {
      return true;
    }
    return equals(pointer, weight.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Get the hash value of a weight.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return hashCode(pointer);
  }

  private native int hashCode(long pointer);
}
