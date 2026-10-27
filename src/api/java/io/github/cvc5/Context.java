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

/**
 * Legacy entry point for releasing native memory.
 *
 * <p>Native memory is now released automatically once the corresponding Java
 * objects are no longer reachable, and can be released deterministically via
 * {@code deletePointer()} or, for term managers, solvers, symbol managers and
 * input parsers, via {@code close()}.</p>
 *
 * @deprecated Native memory is managed automatically. This class will be
 *             removed in a future release.
 */
@Deprecated
public class Context
{
  /**
   * Private constructor to prevent instantiation of this memory management class.
   */
  private Context() {}

  /**
   * Delete all native objects of all term managers, solvers, and objects
   * derived from them, whether or not they are still referenced from Java.
   *
   * <p>This method must be called by a single thread once no term manager and
   * solver instance is in use anymore. Objects whose native counterpart has
   * been deleted must not be used afterwards.</p>
   *
   * @deprecated Native memory is released automatically once the
   *             corresponding Java objects are no longer reachable. Use
   *             {@code deletePointer()} or {@code close()} to release
   *             individual objects deterministically.
   */
  @Deprecated
  public static void deletePointers()
  {
    NativeContext.releaseAll();
  }
}
