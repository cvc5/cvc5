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
 * Identifies the term manager (more precisely, the underlying node manager)
 * that a native object belongs to.
 *
 * <p>One {@code NativeContext} is created per {@link TermManager} and shared by
 * every object derived from it (solvers, terms, sorts, parsers, commands,
 * ...). It carries the per-term-manager memory management state.</p>
 */
final class NativeContext
{
  /** Create the context of a new term manager. */
  NativeContext() {}
}
