/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5.api;

abstract class AbstractPointer implements IPointer
{
  protected final Solver solver;
  protected final long pointer;

  public long getPointer()
  {
    return pointer;
  }

  public Solver getSolver()
  {
    return solver;
  }

  @Override public String toString()
  {
    return toString(pointer);
  }

  abstract protected String toString(long pointer);

  AbstractPointer(Solver solver, long pointer)
  {
    this.solver = solver;
    this.pointer = pointer;
  }
}
