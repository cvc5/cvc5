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
 *
 * IOracle interface for cvc5 oracle functions.
 */

package io.github.cvc5;

/**
 * Functional interface representing an oracle function that operates on an array of
 * {@link Term} objects and produces a single {@link Term} as output.
 */
@FunctionalInterface
public interface IOracle {
  /**
   * Applies the oracle to the given array of {@link Term} arguments.
   *
   * @param terms An array of {@link Term} objects to be used as input to the oracle.
   * @return A {@link Term} representing the result of the oracle computation.
   * @throws CVC5ApiException if an error occurs during term processing or oracle computation.
   */
  Term apply(Term[] terms) throws CVC5ApiException;
}
