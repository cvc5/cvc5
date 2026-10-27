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
 *
 * <p>The native object behind a wrapper is freed automatically once the
 * wrapper is no longer reachable (see {@link NativeContext}), or explicitly
 * via {@link #deletePointer()}.</p>
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
   * Tracks the native object, or {@code null} if it is not tracked.
   */
  private final NativeContext.Ref ref;

  /**
   * Construct an {@code AbstractPointer} with the given native pointer.
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
    this.ref = ctx == null ? null : ctx.register(this, pointer, deleter);
  }

  /**
   * Return the raw native pointer.
   *
   * <p>Every native call obtains the pointers of the objects it uses through
   * this method, so that using an object after its native resource has been
   * released raises an exception instead of crashing the JVM.</p>
   *
   * @return the pointer value
   * @throws IllegalStateException if the native resource of this object has
   *         been released, e.g., via {@link #deletePointer()}
   */
  public long getPointer()
  {
    long p = pointer;
    if (p == 0)
    {
      throw new IllegalStateException(
          "This " + getClass().getSimpleName() + " has been released and cannot be used anymore");
    }
    return p;
  }

  /**
   * Free the native resource associated with this pointer.
   * <p>
   * Native resources are freed automatically once the Java object is no
   * longer reachable. This method frees the native resource immediately
   * instead; afterwards, using the object raises an
   * {@link IllegalStateException}. It must be called from
   * the thread that is using the associated term manager. Calling it more
   * than once has no further effect.
   * </p>
   */
  public void deletePointer()
  {
    if (ref != null)
    {
      pointer = 0;
      ref.release();
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
    return toString(getPointer());
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
