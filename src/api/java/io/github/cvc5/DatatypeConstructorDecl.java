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

import java.lang.foreign.Arena;

/**
 * A cvc5 datatype constructor declaration. A datatype constructor declaration
 * is a specification used for creating a datatype constructor.
 */
public class DatatypeConstructorDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeConstructorDecl(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, DatatypeConstructorDecl::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_dt_cons_decl_release(pointer);
  }

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
    return equals(getPointer(), decl.getPointer());
  }

  private boolean equals(long pointer1, long pointer2)
  {
    return CApi.cvc5_dt_cons_decl_is_equal(pointer1, pointer2);
  }

  /**
   * Add datatype selector declaration.
   * @param name The name of the datatype selector declaration to add.
   * @param sort The codomain sort of the datatype selector declaration to add.
   */
  public void addSelector(String name, Sort sort)
  {
    addSelector(getPointer(), name, sort.getPointer());
  }

  private void addSelector(long pointer, String name, long sortPointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_dt_cons_decl_add_selector(pointer, Native.cstring(arena, name), sortPointer);
    }
  }

  /**
   * Add datatype selector declaration whose codomain type is the datatype
   * itself.
   * @param name The name of the datatype selector declaration to add.
   */
  public void addSelectorSelf(String name)
  {
    addSelectorSelf(getPointer(), name);
  }

  private void addSelectorSelf(long pointer, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_dt_cons_decl_add_selector_self(pointer, Native.cstring(arena, name));
    }
  }

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
    addSelectorUnresolved(getPointer(), name, unresDataypeName);
  }

  private void addSelectorUnresolved(long pointer, String name, String unresDataypeName)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_dt_cons_decl_add_selector_unresolved(
          pointer, Native.cstring(arena, name), Native.cstring(arena, unresDataypeName));
    }
  }

  /**
   * Determine if this DatatypeConstructorDecl is a null declaration.
   *
   * @return True If this DatatypeConstructorDecl is a null declaration.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private boolean isNull(long pointer)
  {
    return pointer == 0;
  }

  /**
   * @return A String representation of this datatype constructor declaration
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_dt_cons_decl_to_string(pointer));
  }

  /**
   * Get the hash value of a datatype constructor declaration.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(getPointer()));
  }

  private long hashCode(long pointer)
  {
    if (pointer == 0)
    {
      return 0;
    }
    return CApi.cvc5_dt_cons_decl_hash(pointer);
  }
}
