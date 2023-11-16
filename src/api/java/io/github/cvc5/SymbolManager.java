/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
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

public class SymbolManager extends AbstractPointer
{
  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package.
   * @param pointer The cpp pointer to symbol manager.
   */
  SymbolManager(long pointer)
  {
    super(pointer);
  }

  public SymbolManager(Solver solver)
  {
    super(newSymbolManager(solver.getPointer()));
  }

  private static native long newSymbolManager(long solverPointer);

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "SymbolManager.toString() is not supported in the cpp api");
  }
  protected native void deletePointer(long pointer);

  @Override
  public boolean equals(Object s)
  {
    if (this == s)
    {
      return true;
    }
    if (s == null || getClass() != s.getClass())
    {
      return false;
    }
    SymbolManager symbolManager = (SymbolManager) s;
    if (this.pointer == symbolManager.pointer)
    {
      return true;
    }
    return false;
  }

  /**
   * @return True if the logic of this symbol manager has been set.
   */
  public boolean isLogicSet()
  {
    return isLogicSet(pointer);
  }

  private native boolean isLogicSet(long pointer);

  /**
   * @api.note Asserts isLogicSet().
   *
   * @return The logic used by this symbol manager.
   */
  public String getLogic()
  {
    return getLogic(pointer);
  }

  private native String getLogic(long pointer);
}
