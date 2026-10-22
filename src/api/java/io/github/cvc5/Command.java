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

import java.lang.ref.Reference;

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
  Command(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, Command::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_cmd_release(pointer);
  }

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
    try
    {
      return invoke(getPointer(), solver.getPointer(), symbolManager.getPointer());
    }
    finally
    {
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable. Keep the
      // solver and symbol manager reachable until the call has returned.
      Reference.reachabilityFence(solver);
      Reference.reachabilityFence(symbolManager);
    }
  }

  private String invoke(long pointer, long solverPointer, long symbolManagerPointer)
  {
    return Native.string(CApi.cvc5_cmd_invoke(pointer, solverPointer, symbolManagerPointer));
  }

  /**
   * @return A string representation of this result.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      // like Command::toString() of the C++ API on a null command
      return "null";
    }
    return Native.string(CApi.cvc5_cmd_to_string(pointer));
  }

  /**
   * Get the name for this command, e.g. "assert".
   *
   * @return The name of this command.
   */
  public String getCommandName()
  {
    return getCommandName(getPointer());
  }

  private String getCommandName(long pointer)
  {
    return Native.string(CApi.cvc5_cmd_get_name(pointer));
  }

  /**
   * Determine if this command is null.
   * @return True if this command is null.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private boolean isNull(long pointer)
  {
    // The C API represents the null command as NULL.
    return pointer == 0;
  }
}
