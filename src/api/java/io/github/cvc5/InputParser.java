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

import static java.lang.foreign.ValueLayout.ADDRESS;

import io.github.cvc5.capi.CApi;
import io.github.cvc5.modes.InputLanguage;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via
 * {@link InputParser#setFileInput(InputLanguage, String)},
 * {@link InputParser#setStringInput(InputLanguage, String, String)},
 * or {@link InputParser#setIncrementalStringInput(InputLanguage, String)} and
 * {@link InputParser#appendIncrementalStringInput(String)}. Then, the methods
 * {@link InputParser#nextCommand()} and {@link InputParser#nextTerm()} can be
 * invoked to parse the input.
 *
 * The input parser interacts with a symbol manager, which determines which
 * symbols are defined in the current context, based on the background logic
 * and user-defined symbols. If no symbol manager is provided, then the
 * input parser will construct (an initially empty) one.
 *
 * If provided, the symbol manager must have a logic that is compatible
 * with the provided solver. That is, if both the solver and symbol
 * manager have their logics set ({@link SymbolManager#isLogicSet()} and
 * {@link Solver#isLogicSet()}, then their logics must be the same.
 *
 * Upon setting an input source, if either the solver (resp. symbol
 * manager) has its logic set, then the symbol manager (resp. solver) is set to
 * use that logic, if its logic is not already set.
 */
public class InputParser extends AbstractPointer implements AutoCloseable
{
  /**
   * The solver of this parser. The native parser only borrows the native
   * solver, so the wrapper is kept reachable here.
   */
  private final Solver d_solver;
  /**
   * The symbol manager of this parser, kept reachable for the same reason as
   * {@link #d_solver}.
   */
  private final SymbolManager d_sm;

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
    super(solver.ctx, newInputParser(solver.handle(), sm.handle()), InputParser::deletePointer);
    d_solver = solver;
    d_sm = sm;
  }

  private static MemorySegment newInputParser(
      MemorySegment solverPointer, MemorySegment symbolManagerPointer)
  {
    return Native.handle(CApi.cvc5_parser_new(solverPointer, symbolManagerPointer));
  }

  /**
   * Construct an input parser with an initially empty symbol manager.
   *
   * @param solver The solver (e.g. for constructing terms and sorts).
   */
  public InputParser(Solver solver)
  {
    // unlike cpp api, here we create a symbol manager first and then
    // we call the corresponding constructor in cpp api
    this(solver, new SymbolManager(solver.getTermManager()));
  }

  private static void deletePointer(MemorySegment pointer)
  {
    // Not cvc5_parser_release(), which would invalidate the commands that are
    // still in use. Commands keep the native parser alive until they are
    // released themselves.
    CApi.cvc5_parser_delete(pointer);
  }

  /**
   * Free the native input parser, see {@code deletePointer()}.
   */
  @Override
  public void close()
  {
    deletePointer();
  }

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "InputParser.toString() is not supported in the cpp api");
  }

  /**
   * Get the underlying solver of this input parser.
   *
   * @return The underlying solver of this input parser
   */
  public Solver getSolver()
  {
    return d_solver;
  }

  /**
   * Get the underlying symbol manager of this input parser.
   *
   * @return The underlying symbol manager of this input parser.
   */
  public SymbolManager getSymbolManager()
  {
    return d_sm;
  }

  /**
   * Set the input for the given file.
   *
   * @param lang the input language (e.g. InputLanguage.SMT_LIB_2_6).
   * @param fileName the input file name.
   */
  public void setFileInput(InputLanguage lang, String fileName)
  {
    setFileInput(handle(), lang.getValue(), fileName);
  }

  private void setFileInput(MemorySegment pointer, int langValue, String fileName)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_parser_set_file_input(pointer, langValue, arena.allocateFrom(fileName));
      Native.check();
    }
  }

  /**
   * Set the input to the given concrete input string.
   *
   * @param lang The input language.
   * @param input The input string.
   * @param name The name of the stream, for use in error messages.
   */
  public void setStringInput(InputLanguage lang, String input, String name)
  {
    setStringInput(handle(), lang.getValue(), input, name);
  }
  private void setStringInput(MemorySegment pointer, int langValue, String input, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_parser_set_str_input(
          pointer, langValue, arena.allocateFrom(input), arena.allocateFrom(name));
      Native.check();
    }
  }

  /**
   * Set that we will be feeding strings to this parser via
   * appendIncrementalStringInput below.
   *
   * @param lang The input language.
   * @param name The name of the stream, for use in error messages.
   */
  public void setIncrementalStringInput(InputLanguage lang, String name)
  {
    setIncrementalStringInput(handle(), lang.getValue(), name);
  }

  private void setIncrementalStringInput(MemorySegment pointer, int langValue, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_parser_set_inc_str_input(pointer, langValue, arena.allocateFrom(name));
      Native.check();
    }
  }

  /**
   * Append string to the input being parsed by this parser. Should be
   * called after calling setIncrementalStringInput.
   *
   * @param input The input string.
   */
  public void appendIncrementalStringInput(String input)
  {
    appendIncrementalStringInput(handle(), input);
  }

  private void appendIncrementalStringInput(MemorySegment pointer, String input)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_parser_append_inc_str_input(pointer, arena.allocateFrom(input));
      Native.check();
    }
  }

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
    return new Command(ctx, nextCommand(handle()));
  }

  private MemorySegment nextCommand(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment errorMsg = arena.allocate(ADDRESS);
      MemorySegment cmd = Native.handle(CApi.cvc5_parser_next_command(pointer, errorMsg));
      checkParseError(errorMsg);
      return cmd;
    }
  }

  /**
   * Parse and return the next term. Requires setting the logic prior
   * to this point.
   * @return The parsed term.
   */
  public Term nextTerm()
  {
    return new Term(ctx, nextTerm(handle()));
  }

  private MemorySegment nextTerm(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment errorMsg = arena.allocate(ADDRESS);
      MemorySegment term = Native.handle(CApi.cvc5_parser_next_term(pointer, errorMsg));
      checkParseError(errorMsg);
      return term;
    }
  }

  /**
   * Raise the parse error reported by {@code cvc5_parser_next_command()} or
   * {@code cvc5_parser_next_term()}, if any.
   *
   * <p>These functions report parse errors through their {@code error_msg}
   * output parameter rather than the error state of the C API (other errors
   * are reported through both, and {@link Native#handle} raises them). A
   * parse error raises a {@link CVC5ParserException}, which is a checked
   * exception, regardless of whether the calling method declares it, as the
   * native methods did when the Java API was based on JNI.</p>
   *
   * @param errorMsg The {@code error_msg} output parameter.
   */
  private static void checkParseError(MemorySegment errorMsg)
  {
    MemorySegment msg = errorMsg.get(ADDRESS, 0);
    if (msg.address() != 0)
    {
      throw InputParser.<RuntimeException>sneakyThrow(
          new CVC5ParserException(Native.copyString(msg)));
    }
  }

  @SuppressWarnings("unchecked")
  private static <T extends Throwable> T sneakyThrow(Throwable t) throws T
  {
    throw (T) t;
  }

  /**
   * Determine if this parser done reading input.
   *
   * @return True if this parser done reading input.
   */
  public boolean done()
  {
    return done(handle());
  }

  private boolean done(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_parser_done(pointer));
  }
}
