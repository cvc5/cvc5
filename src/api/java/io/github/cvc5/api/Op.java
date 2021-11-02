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

public class Op extends AbstractPointer
{
  // region construction and destruction
  Op(Solver solver, long pointer)
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
   * Syntactic equality operator.
   * Return true if both operators are syntactically identical.
   * Both operators must belong to the same solver object.
   * @param t the operator to compare to for equality
   * @return true if the operators are equal
   */
  @Override public boolean equals(Object t)
  {
    if (this == t)
      return true;
    if (t == null || getClass() != t.getClass())
      return false;
    return equals(pointer, ((Op) t).getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * @return the kind of this operator
   */
  public Kind getKind()
  {
    try
    {
      int value = getKind(pointer);
      return Kind.fromInt(value);
    }
    catch (CVC5ApiException e)
    {
      e.printStackTrace();
      throw new RuntimeException(e.getMessage());
    }
  }

  private native int getKind(long pointer);

  /**
   * @return true if this operator is a null term
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return true iff this operator is indexed
   */
  public boolean isIndexed()
  {
    return isIndexed(pointer);
  }

  private native boolean isIndexed(long pointer);

  /**
   * @return the number of indices of this op
   */
  public int getNumIndices()
  {
    return getNumIndices(pointer);
  }

  private native int getNumIndices(long pointer);

  /**
   * Get the indices used to create this Op.
   * Check the Op Kind with getKind() to determine which argument to use.
   *
   * @return the indices used to create this Op
   */
  public int[] getIntegerIndices()
  {
    return getIntegerIndices(pointer);
  }

  private native int[] getIntegerIndices(long pointer);

  /**
   * Get the indices used to create this Op.
   * Check the Op Kind with getKind() to determine which argument to use.
   *
   * @return the indices used to create this Op
   */
  public String[] getStringIndices()
  {
    return getStringIndices(pointer);
  }

  private native String[] getStringIndices(long pointer);

  /**
   * @return a string representation of this operator
   */
  protected native String toString(long pointer);
}
