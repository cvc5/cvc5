/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
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
 * Encapsulation of a command.
 *
 * Commands are constructed by the input parser and can be invoked on
 * the solver and symbol manager.
 */
public class Command extends AbstractPointer
{
  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package.
   * @param pointer The cpp pointer to command.
   */
  Command(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  /**
   * Invoke the command on the solver and symbol manager sm and return any
   * resulting output as a string.
   *
   * @param solver The solver to invoke the command on.
   * @param symbolManager The symbol manager to invoke the command on.
   * @return The output of invoking the command.
   */
  public String invoke(Solver solver, SymbolManager symbolManager)
  {
    return invoke(pointer, solver.getPointer(), symbolManager.getPointer());
  }

  private native String invoke(long pointer, long solverPointer, long symbolManagerPointer);

  /**
   * @return A string representation of this result.
   */
  protected native String toString(long pointer);

  /**
   * Get the name for this command, e.g. "assert".
   *
   * @return The name of this command.
   */
  public String getCommandName()
  {
    return getCommandName(pointer);
  }

  private native String getCommandName(long pointer);

  /**
   * Determine if this command is null.
   * @return True if this command is null.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);
}
