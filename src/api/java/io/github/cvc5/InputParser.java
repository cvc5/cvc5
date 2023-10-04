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

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via e.g.
 * setFileInput, setStreamInput, or setIncrementalStringInput and
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
 * manager have their logics set (SymbolManager::isLogicSet and
 * Solver::isLogicSet), then their logics must be the same.
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
   * @param solver The solver (e.g. for constructing terms and sorts)
   */
  public InputParser(Solver solver)
  {
    super(newInputParser(solver.getPointer()));
  }

  private static native long newInputParser(long solverPointer);

  /**
   * @return The underlying solver of this input parser
   */
  Solver getSolver()
  {
    return null;
  }

  protected native void deletePointer(long pointer);

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "InputParser.toString() is not supported in the cpp api");
  }

  /**
   * Syntactic equality operator.
   * Return true if both terms are syntactically identical.
   * Both terms must belong to the same solver object.
   *
   * @param t The term to compare to for equality.
   * @return True if the terms are equal.
   */
  @Override
  public boolean equals(Object t)
  {
    if (this == t)
      return true;
    if (t == null || getClass() != t.getClass())
      return false;
    Term term = (Term) t;
    if (this.pointer == term.pointer)
    {
      return true;
    }
    return equals(pointer, term.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * @return The underlying symbol manager of this input parser
   */
  SymbolManager getSymbolManager()
  {
    return null;
  }

  /**
   * Set the input for the given file.
   *
   * @param lang the input language (e.g. modes::InputLanguage::SMT_LIB_2_6)
   * @param filename the input filename
   */
  // void setFileInput(modes::InputLanguage lang, String filename) {}

  /**
   * Set that we will be feeding strings to this parser via
   * appendIncrementalStringInput below.
   *
   * @param lang the input language
   * @param name the name of the stream, for use in error messages
   */
  // void setIncrementalStringInput(modes::InputLanguage lang, String name);

  /**
   * Append string to the input being parsed by this parser. Should be
   * called after calling setIncrementalStringInput and only after the
   * previous string (if one was provided) is finished being parsed.
   *
   * @param input The input string
   */
  void appendIncrementalStringInput(String input) {}

  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   *
   * @return The parsed command. This is the null command if no command was
   *         read.
   */
  Command nextCommand()
  {
    return null;
  }

  /**
   * Parse and return the next term. Requires setting the logic prior
   * to this point.
   */
  Term nextTerm()
  {
    return null;
  }

  /** Is this parser done reading input? */
  boolean done()
  {
    return false;
  }
}
