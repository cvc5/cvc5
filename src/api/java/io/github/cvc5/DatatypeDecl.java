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

import io.github.cvc5.capi.CApi;
import java.lang.foreign.MemorySegment;

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
    super(null, MemorySegment.NULL, null);
  }

  DatatypeDecl(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, DatatypeDecl::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_dt_decl_release(pointer);
  }

  /**
   * Syntactic equality operator.
   *
   * @param d The datatype declaration to compare to for equality.
   * @return True if the datatype declarations are equal.
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
    DatatypeDecl decl = (DatatypeDecl) d;
    if (address() == decl.address())
    {
      return true;
    }
    return equals(handle(), decl.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_dt_decl_is_equal(pointer1, pointer2));
  }

  /**
   * Add datatype constructor declaration.
   * @param ctor The datatype constructor declaration to add.
   */
  public void addConstructor(DatatypeConstructorDecl ctor)
  {
    addConstructor(handle(), ctor.handle());
  }

  private void addConstructor(MemorySegment pointer, MemorySegment declPointer)
  {
    CApi.cvc5_dt_decl_add_constructor(pointer, declPointer);
    Native.check();
  }

  /**
   * Get the number of constructors (so far) for this Datatype declaration.
   * @return The number of constructors.
   */
  public int getNumConstructors()
  {
    return getNumConstructors(handle());
  }

  private int getNumConstructors(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_dt_decl_get_num_constructors(pointer));
  }

  /**
   * Determine if this datatype declaration is parametric.
   * @return True if this DatatypeDecl is parametric.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public boolean isParametric()
  {
    return isParametric(handle());
  }

  private boolean isParametric(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_decl_is_parametric(pointer));
  }

  /**
   * Determine if this DatatypeDecl is a null object.
   *
   * @return True if this DatatypeDecl is a null object.
   */
  public boolean isNull()
  {
    return isNull(handle());
  }

  private boolean isNull(MemorySegment pointer)
  {
    return pointer.address() == 0;
  }

  /**
   * @return A string representation of this datatype declaration.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_dt_decl_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * Get the name of this datatype declaration.
   *
   * @return The name of this datatype declaration.
   */
  public String getName()
  {
    return getName(handle());
  }

  private String getName(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_dt_decl_get_name(pointer));
  }

  /**
   * Get the hash value of a datatype declaration.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(handle()));
  }

  private long hashCode(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      return 0;
    }
    return Native.check(CApi.cvc5_dt_decl_hash(pointer));
  }
}
