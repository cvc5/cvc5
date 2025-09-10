/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

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
   * Return the raw native pointer.
   *
   * @return the pointer value
  */
  public long getPointer()
  {
    return pointer;
  }

  /**
   * Delete the native resource associated with the specified pointer.
   * <p>
   * Subclasses must implement this method to provide resource-specific cleanup logic.
   * </p>
   *
   * @param pointer the native pointer to delete
   */
  protected abstract void deletePointer(long pointer);

  /**
   * Free the native resource associated with this pointer.
   * <p>
   * This method should be called to explicitly clean up the underlying native resource.
   * It removes this instance from the {@code Context}, then invokes the subclass-defined
   * {@link #deletePointer(long)} method to perform the actual cleanup.
   * </p>
   */
  public void deletePointer()
  {
    if (pointer != 0)
    {
      Context.removeAbstractPointer(this);
      deletePointer(pointer);
    }
    pointer = 0;
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

  /**
   * Construct an {@code AbstractPointer} with the given native pointer.
   * Automatically registers this instance with the {@code Context}.
   *
   * @param pointer the native pointer to wrap
  */
  AbstractPointer(long pointer)
  {
    this.pointer = pointer;
    Context.addAbstractPointer(this);
  }
}
