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

public class DatatypeConstructorDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeConstructorDecl(Solver solver, long pointer)
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
   * Add datatype selector declaration.
   * @param name the name of the datatype selector declaration to add
   * @param sort the codomain sort of the datatype selector declaration to add
   */
  public void addSelector(String name, Sort sort)
  {
    addSelector(pointer, name, sort.getPointer());
  }

  private native void addSelector(long pointer, String name, long sortPointer);

  /**
   * Add datatype selector declaration whose codomain type is the datatype
   * itself.
   * @param name the name of the datatype selector declaration to add
   */
  public void addSelectorSelf(String name)
  {
    addSelectorSelf(pointer, name);
  }

  private native void addSelectorSelf(long pointer, String name);

  /**
   * @return true if this DatatypeConstructorDecl is a null declaration.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return a string representation of this datatype constructor declaration
   */
  protected native String toString(long pointer);
}
