/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

/**
 * A cvc5 datatype constructor declaration. A datatype constructor declaration
 * is a specification used for creating a datatype constructor.
 */
public class DatatypeConstructorDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeConstructorDecl(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  // endregion

  /**
   * Syntactic equality operator.
   *
   * @param d The datatype constructor declaration to compare to for equality.
   * @return True if the datatype constructor declarations are equal.
   */
  @Override
  public boolean equals(Object d)
  {
    if (this == d)
    {
      return true;
    }
    if (d == null || getClass() != d.getClass())
    {
      return false;
    }
    DatatypeConstructorDecl decl = (DatatypeConstructorDecl) d;
    if (this.pointer == decl.pointer)
    {
      return true;
    }
    return equals(pointer, decl.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Add datatype selector declaration.
   * @param name The name of the datatype selector declaration to add.
   * @param sort The codomain sort of the datatype selector declaration to add.
   */
  public void addSelector(String name, Sort sort)
  {
    addSelector(pointer, name, sort.getPointer());
  }

  private native void addSelector(long pointer, String name, long sortPointer);

  /**
   * Add datatype selector declaration whose codomain type is the datatype
   * itself.
   * @param name The name of the datatype selector declaration to add.
   */
  public void addSelectorSelf(String name)
  {
    addSelectorSelf(pointer, name);
  }

  private native void addSelectorSelf(long pointer, String name);

  /**
   * Add datatype selector declaration whose codomain sort is an unresolved
   * datatype with the given name.
   * @param name The name of the datatype selector declaration to add.
   * @param unresDataypeName The name of the unresolved datatype. The codomain
   *                         of the selector will be the resolved datatype with
   *                         the given name.
   */
  public void addSelectorUnresolved(String name, String unresDataypeName)
  {
    addSelectorUnresolved(pointer, name, unresDataypeName);
  }

  private native void addSelectorUnresolved(long pointer, String name, String unresDataypeName);

  /**
   * Determine if this DatatypeConstructorDecl is a null declaration.
   *
   * @return True If this DatatypeConstructorDecl is a null declaration.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return A String representation of this datatype constructor declaration
   */
  protected native String toString(long pointer);

  /**
   * Get the hash value of a datatype constructor declaration.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return hashCode(pointer);
  }

  private native int hashCode(long pointer);
}
