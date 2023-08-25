/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
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

  public long getPointer()
  {
    return pointer;
  }

  // endregion

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
}
