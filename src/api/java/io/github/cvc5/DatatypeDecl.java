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
 * A cvc5 datatype declaration. A datatype declaration is not itself a datatype
 * (see {@link Datatype}), but a specification for creating a datatype sort.
 *
 * The interface for a datatype declaration coincides with the syntax for the
 * SMT-LIB 2.6 command {@code declare-datatype}, or a single datatype within the
 * {@code declare-datatypes} command.
 *
 * Datatype sorts can be constructed from DatatypeDecl using the methods:
 *   - {@link Solver#mkDatatypeSort(DatatypeDecl)}
 *   - {@link Solver#mkDatatypeSorts(DatatypeDecl[])}
 */
public class DatatypeDecl extends AbstractPointer
{
  /**
   * Null datatypeDecl
   */
  public DatatypeDecl()
  {
    super(getNullDatatypeDecl());
  }

  private static native long getNullDatatypeDecl();

  DatatypeDecl(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  /**
   * Add datatype constructor declaration.
   * @param ctor The datatype constructor declaration to add.
   */
  public void addConstructor(DatatypeConstructorDecl ctor)
  {
    addConstructor(pointer, ctor.getPointer());
  }

  private native void addConstructor(long pointer, long declPointer);

  /** Get the number of constructors (so far) for this Datatype declaration. */
  public int getNumConstructors()
  {
    return getNumConstructors(pointer);
  }

  private native int getNumConstructors(long pointer);

  /**
   * @return True if this DatatypeDecl is parametric.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public boolean isParametric()
  {
    return isParametric(pointer);
  }

  private native boolean isParametric(long pointer);

  /**
   * @return True if this DatatypeDecl is a null object.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return A string representation of this datatype declaration.
   */
  protected native String toString(long pointer);

  /** @return The name of this datatype declaration. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);
}
