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

import java.util.function.LongConsumer;

/**
 * Abstract base class for handling native pointers in a managed way.
 */
abstract class AbstractPointer implements IPointer
{
  /**
   * The raw native pointer value.
   */
  protected long pointer;

  /**
   * The context of the term manager this object belongs to, or {@code null}
   * for null objects, which are not associated with any term manager and
   * share a single, static native object per class.
   */
  final NativeContext ctx;

  /**
   * The function that frees the native object, or {@code null} if it is
   * never freed.
   */
  private final LongConsumer deleter;

  /**
   * Construct an {@code AbstractPointer} with the given native pointer.
   * Automatically registers this instance with the {@code Context}, unless it
   * is a null object.
   *
   * @param ctx the context of the term manager the native object belongs to,
   *            or {@code null} if the native object is a static null object
   *            that is never freed
   * @param pointer the native pointer to wrap
   * @param deleter the function that frees the native object
   */
  AbstractPointer(NativeContext ctx, long pointer, LongConsumer deleter)
  {
    this.pointer = pointer;
    this.ctx = ctx;
    this.deleter = deleter;
    if (ctx != null)
    {
      Context.addAbstractPointer(this);
    }
  }

  /**
   * Return the raw native pointer.
   *
   * @return the pointer value
   */
  public long getPointer()
  {
    return pointer;
  }

  /**
   * Free the native resource associated with this pointer.
   * <p>
   * This method should be called to explicitly clean up the underlying native
   * resource. It removes this instance from the {@code Context}, then frees
   * the native object. Calling it more than once has no further effect.
   * </p>
   */
  public void deletePointer()
  {
    if (pointer != 0 && deleter != null)
    {
      Context.removeAbstractPointer(this);
      deleter.accept(pointer);
      pointer = 0;
    }
  }

  /**
   * Return a string representation of the pointer.
   *
   * @return a string representation of the pointer
   */
  @Override
  public String toString()
  {
    return toString(pointer);
  }

  /**
   * Return a string representation of the specified native pointer.
   * <p>
   * Subclasses must implement this method to convert the native pointer
   * into a meaningful string.
   * </p>
   *
   * @param pointer the native pointer
   * @return a string representation of the pointer
   */
  abstract protected String toString(long pointer);
}
