/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
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
 */

package io.github.cvc5;

abstract class AbstractPointer implements IPointer
{
  protected long pointer;

  public long getPointer()
  {
    return pointer;
  }

  protected abstract void deletePointer(long pointer);

  public void deletePointer()
  {
    if (pointer != 0)
    {
      deletePointer(pointer);
    }
    pointer = 0;
  }

  @Override
  public String toString()
  {
    return toString(pointer);
  }

  abstract protected String toString(long pointer);

  AbstractPointer(long pointer)
  {
    this.pointer = pointer;
    Context.addAbstractPointer(this);
  }
}
