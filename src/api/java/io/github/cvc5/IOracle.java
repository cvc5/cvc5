/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

@FunctionalInterface
public interface IOracle {
  Term apply(Term[] terms) throws CVC5ApiException;
}
