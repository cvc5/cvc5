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

import java.lang.foreign.MemorySegment;
import java.util.function.Consumer;

/**
 * Abstract base class for handling native pointers in a managed way.
 *
 * <p>The native object behind a wrapper is freed automatically once the
 * wrapper is no longer reachable (see {@link NativeContext}), or explicitly
 * via {@link #deletePointer()}.</p>
 */
abstract class AbstractPointer implements IPointer
{
  static
  {
    // The bindings look up each C function on its first call, and a failed
    // lookup cannot be retried: load the libraries before any wrapper class
    // can call the C API, even for null objects.
    Utils.loadLibraries();
  }

  /**
   * The handle of the native object in the cvc5 C API, or
   * {@link MemorySegment#NULL} for null objects (e.g., {@code new Term()}) and
   * for objects whose native object has been released.
   */
  private MemorySegment handle;

  /**
   * The context of the term manager this object belongs to, or {@code null}
   * for null objects, which are not associated with any term manager.
   */
  final NativeContext ctx;

  /**
   * Tracks the native object, or {@code null} if it is not tracked.
   */
  private final NativeContext.Ref ref;

  /**
   * Construct an {@code AbstractPointer} with the given native handle.
   *
   * <p>The wrapper owns one reference to the native object, which the C API
   * returned to it, and releases it once the wrapper is unreachable or
   * {@link #deletePointer()} is called. A NULL handle represents a null
   * object, which is not tracked.</p>
   *
   * @param ctx the context of the term manager the native object belongs to,
   *            or {@code null} for a null object
   * @param handle the handle of the native object, or NULL for a null object
   * @param deleter the function that releases the native object, or
   *                {@code null} if this wrapper does not own a reference to
   *                it (e.g., {@link Solver#getTermManager()})
   */
  AbstractPointer(NativeContext ctx, MemorySegment handle, Consumer<MemorySegment> deleter)
  {
    this.handle = handle;
    this.ctx = handle.address() == 0 ? null : ctx;
    this.ref =
        this.ctx == null || deleter == null ? null : this.ctx.register(this, handle, deleter);
  }

  /**
   * Return the handle of the native object, to be passed to the C API.
   *
   * <p>Every native call obtains the handles of the objects it uses through
   * this method, so that using an object after its native resource has been
   * released raises an exception instead of crashing the JVM.</p>
   *
   * @return the handle, which is NULL for null objects
   * @throws IllegalStateException if the native resource of this object has
   *         been released, e.g., via {@link #deletePointer()}
   */
  final MemorySegment handle()
  {
    MemorySegment h = handle;
    if (h.address() == 0 && ref != null)
    {
      throw new IllegalStateException(
          "This " + getClass().getSimpleName() + " has been released and cannot be used anymore");
    }
    return h;
  }

  /**
   * Return the address of the native object, without checking whether it has
   * been released (e.g., for comparisons).
   *
   * @return the address, which is 0 for null and released objects
   */
  final long address()
  {
    return handle.address();
  }

  /**
   * Return the raw native pointer.
   *
   * @return the address of the native object, which is 0 for null objects
   * @throws IllegalStateException if the native resource of this object has
   *         been released, e.g., via {@link #deletePointer()}
   */
  public long getPointer()
  {
    return handle().address();
  }

  /** Mark the native object as released. */
  final void clear()
  {
    handle = MemorySegment.NULL;
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
      clear();
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
