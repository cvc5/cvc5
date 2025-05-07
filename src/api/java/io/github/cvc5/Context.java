/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
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

import java.util.ArrayList;
import java.util.List;

/**
 * The {@code Context} class is responsible for tracking and deleting pointers to
 * native C++ cvc5 objects associated with their corresponding Java counterparts.
 *
 * <p>This class maintains a centralized registry of {@link AbstractPointer}
 * instances, such as those used for term managers, solvers, terms, sorts, etc and
 * ensures that all native memory is properly released when no longer needed.</p>
 */
public class Context
{
  // Store pointers for term managers, solvers, terms, sorts, etc
  private static final List<AbstractPointer> abstractPointers = new ArrayList<>();

  /**
     * Registers a new {@link AbstractPointer} for later cleanup.
     *
     * <p>If the pointer is already registered, it will not be added again.</p>
     *
     * @param pointer the {@link AbstractPointer} to register
     */
  static void addAbstractPointer(AbstractPointer pointer)
  {
    synchronized (abstractPointers)
    {
      if (!abstractPointers.contains(pointer))
      {
        abstractPointers.add(pointer);
      }
    }
  }

  /**
   * Deletes all registered native pointers in reverse order of their registration.
   *
   * <p>This method should be called by a single thread once all term managers and
   * solver instances are no longer needed. It ensures that all native memory
   * associated with registered {@link AbstractPointer}s is released to
   * prevent memory leaks.</p>
   *
   * <p>For more fine-grained control over memory release, consider using
   * the {@link AbstractPointer#deletePointer()} method individually on
   * each Java object instead of calling this method.</p>
   */
  public static void deletePointers()
  {
    synchronized (abstractPointers)
    {
      for (int i = abstractPointers.size() - 1; i >= 0; i--)
      {
        abstractPointers.get(i).deletePointer();
      }
      abstractPointers.clear();
    }
  }
}
