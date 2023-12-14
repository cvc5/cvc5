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

import io.github.cvc5.modes.InputLanguage;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via e.g.
 * setFileInput, setStringInput, or setIncrementalStringInput and
 * appendIncrementalStringInput. Then, the methods nextCommand and
 * nextExpression can be invoked to parse the input.
 *
 * The input parser interacts with a symbol manager, which determines which
 * symbols are defined in the current context, based on the background logic
 * and user-defined symbols. If no symbol manager is provided, then the
 * input parser will construct (an initially empty) one.
 *
 * If provided, the symbol manager must have a logic that is compatible
 * with the provided solver. That is, if both the solver and symbol
 * manager have their logics set (SymbolManager.isLogicSet and
 * {@link Solver#isLogicSet()}, then their logics must be the same.
 *
 * Upon setting an input source, if either the solver (resp. symbol
 * manager) has its logic set, then the symbol manager (resp. solver) is set to
 * use that logic, if its logic is not already set.
 */
public class InputParser extends AbstractPointer
{
  /**
   * Construct an input parser
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   * @param sm The symbol manager, which contains a symbol table that maps
   * symbols to terms and sorts. Must have a logic that is compatible
   * with the solver.
   */
  public InputParser(Solver solver, SymbolManager sm)
  {
    super(newInputParser(solver.getPointer(), sm.getPointer()));
  }

  private static native long newInputParser(long solverPointer, long symbolManagerPointer);

  /**
   * Construct an input parser with an initially empty symbol manager.
   *
   * @param solver The solver (e.g. for constructing terms and sorts).
   */
  public InputParser(Solver solver)
  {
    // unlike cpp api, here we create a symbol manager first and then
    // we call the corresponding constructor in cpp api
    super(newInputParser(solver.getPointer(), new SymbolManager(solver).getPointer()));
  }

  private static native long newInputParser(long solverPointer);

  protected native void deletePointer(long pointer);

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "InputParser.toString() is not supported in the cpp api");
  }

  /**
   * @return The underlying solver of this input parser
   */
  public Solver getSolver()
  {
    return new Solver(getSolver(pointer));
  }

  private native long getSolver(long pointer);

  /**
   * @return The underlying symbol manager of this input parser.
   */
  public SymbolManager getSymbolManager()
  {
    return new SymbolManager(getSymbolManager(pointer));
  }

  private native long getSymbolManager(long pointer);

  /**
   * Set the input for the given file.
   *
   * @param lang the input language (e.g. InputLanguage.SMT_LIB_2_6).
   * @param fileName the input file name.
   */
  public void setFileInput(InputLanguage lang, String fileName)
  {
    setFileInput(pointer, lang.getValue(), fileName);
  }

  private native void setFileInput(long pointer, int langValue, String fileName);

  /**
   * Set the input to the given concrete input string.
   *
   * @param lang The input language.
   * @param input The input string.
   * @param name The name of the stream, for use in error messages.
   */
  public void setStringInput(InputLanguage lang, String input, String name)
  {
    setStringInput(pointer, lang.getValue(), input, name);
  }
  private native void setStringInput(long pointer, int langValue, String input, String name);

  /**
   * Set that we will be feeding strings to this parser via
   * appendIncrementalStringInput below.
   *
   * @param lang The input language.
   * @param name The name of the stream, for use in error messages.
   */
  public void setIncrementalStringInput(InputLanguage lang, String name)
  {
    setIncrementalStringInput(pointer, lang.getValue(), name);
  }

  private native void setIncrementalStringInput(long pointer, int langValue, String name);

  /**
   * Append string to the input being parsed by this parser. Should be
   * called after calling setIncrementalStringInput.
   *
   * @param input The input string.
   */
  public void appendIncrementalStringInput(String input)
  {
    appendIncrementalStringInput(pointer, input);
  }

  private native void appendIncrementalStringInput(long pointer, String input);

  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   *
   * @return The parsed command. This is the null command if no command was
   *         read.
   */
  public Command nextCommand()
  {
    return new Command(nextCommand(pointer));
  }

  private native long nextCommand(long pointer);

  /**
   * Parse and return the next term. Requires setting the logic prior
   * to this point.
   */
  public Term nextTerm()
  {
    return new Term(nextTerm(pointer));
  }

  private native long nextTerm(long pointer);

  /** @return True if this parser done reading input. */
  public boolean done()
  {
    return done(pointer);
  }

  private native boolean done(long pointer);
}
