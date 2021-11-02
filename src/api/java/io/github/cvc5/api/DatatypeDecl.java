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

public class DatatypeDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeDecl(Solver solver, long pointer)
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
   * Add datatype constructor declaration.
   * @param ctor the datatype constructor declaration to add
   */
  public void addConstructor(DatatypeConstructorDecl ctor)
  {
    addConstructor(pointer, ctor.getPointer());
  }

  private native void addConstructor(long pointer, long declPointer);

  /** Get the number of constructors (so far) for this Datatype declaration. */
  int getNumConstructors()
  {
    return getNumConstructors(pointer);
  }

  private native int getNumConstructors(long pointer);

  /** Is this Datatype declaration parametric? */
  public boolean isParametric()
  {
    return isParametric(pointer);
  }

  private native boolean isParametric(long pointer);

  /**
   * @return true if this DatatypeDecl is a null object
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return a string representation of this datatype declaration
   */
  protected native String toString(long pointer);

  /** @return the name of this datatype declaration. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);
}
