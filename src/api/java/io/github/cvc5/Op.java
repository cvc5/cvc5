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
 * A cvc5 operator.
 *
 * An operator is a term that represents certain operators, instantiated
 * with its required parameters, e.g., a Term of kind
 * {@link Kind#BITVECTOR_EXTRACT}.
 */
public class Op extends AbstractPointer
{
  /**
   * Null op
   */
  public Op()
  {
    super(null, MemorySegment.NULL, null);
  }

  Op(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, Op::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_op_release(pointer);
  }

  /**
   * Syntactic equality operator.
   * @param t The operator to compare to for equality.
   * @return True if the operators are syntactically identical.
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
    return equals(handle(), ((Op) t).handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_op_is_equal(pointer1, pointer2));
  }

  /**
   * Get the kind of this operator.
   *
   * @return The kind of this operator.
   */
  public Kind getKind()
  {
    try
    {
      int value = getKind(handle());
      return Kind.fromInt(value);
    }
    catch (CVC5ApiException e)
    {
      e.printStackTrace();
      throw new RuntimeException(e.getMessage());
    }
  }

  private int getKind(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_op_get_kind(pointer));
  }

  /**
   * Determine if this operator is a null term.
   *
   * @return True if this operator is a null term.
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
   * Determine if this operator is indexed.
   *
   * @return True iff this operator is indexed.
   */
  public boolean isIndexed()
  {
    return isIndexed(handle());
  }

  private boolean isIndexed(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // The C API rejects null operators, which are not indexed.
      return false;
    }
    return Native.check(CApi.cvc5_op_is_indexed(pointer));
  }

  /**
   * Get the number of indices of this op.
   *
   * @return The number of indices of this op.
   */
  public int getNumIndices()
  {
    return getNumIndices(handle());
  }

  private int getNumIndices(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_op_get_num_indices(pointer));
  }

  /**
   * Get the index at position {@code i}.
   * @param i The position of the index to return.
   * @return The index at position {@code i}.
   * @throws CVC5ApiException on error
   */
  public Term get(int i) throws CVC5ApiException
  {
    Utils.validateUnsigned(i, "index");
    MemorySegment termPointer = get(handle(), i);
    return new Term(ctx, termPointer);
  }

  private MemorySegment get(MemorySegment pointer, int i)
  {
    return Native.handle(CApi.cvc5_op_get_index(pointer, i));
  }

  /**
   * @return A string representation of this operator.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      // The C API rejects null operators, whose string representation is the
      // name of their kind.
      return Kind.NULL_TERM.name();
    }
    return Native.string(CApi.cvc5_op_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * Get the hash value of an operator.
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
      // The C API rejects null operators, whose hash value is the value of their
      // kind.
      return Kind.NULL_TERM.getValue();
    }
    return Native.check(CApi.cvc5_op_hash(pointer));
  }
}
