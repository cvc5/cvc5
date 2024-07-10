/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C Parser API.
 */

#ifndef CVC5__C_API__CVC5_PARSER_H
#define CVC5__C_API__CVC5_PARSER_H

#include <cvc5/c/cvc5.h>
#include <cvc5/cvc5_export.h>

#if __cplusplus
extern "C" {
#endif

/* -------------------------------------------------------------------------- */

/**
 * Symbol manager. Internally, the symbol manager manages a symbol table and
 * other meta-information pertaining to SMT2 file inputs (e.g. named
 * assertions, declared functions, etc.).
 *
 * A symbol manager can be modified by invoking commands, see
 * `cvc5_command_invoke()`.
 *
 * A symbol manager can be provided when constructing a Cvc5InputParser, in
 * which case that input parser has symbols of this symbol manager preloaded.
 *
 * The symbol manager's interface is otherwise not publicly available.
 */
typedef struct Cvc5SymbolManager Cvc5SymbolManager;

/**
 * Encapsulation of a command.
 *
 * Commands are constructed by the input parser and can be invoked on
 * the solver and symbol manager.
 */
typedef struct cvc5_cmd_t* Cvc5Command;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first configure via,
 * e.g., `cvc5_parser_set_file_input()`, `cvc5_parser_set_stream_input()`
 * `cvc5_parser_set_str_input()` or `cvc5_parser_set_inc_str_input()` and
 * `cvc5_parser_append_inc_str_input()`.
 * Then, functions `cvc5_parser_next_command()` and
 * `cvc5_parser_next_expression()` can be invoked to parse the input.
 *
 * The input parser interacts with a symbol manager, which determines which
 * symbols are defined in the current context, based on the background logic
 * and user-defined symbols. If no symbol manager is provided, then the
 * input parser will construct (an initially empty) one.
 *
 * If provided, the symbol manager must have a logic that is compatible
 * with the provided solver. That is, if both the solver and symbol
 * manager have their logics set (`cvc5_sm_is_logic_set()` and
 * `cvc5_is_logic_set()`), then their logics must be the same.
 *
 * Upon setting an input source, if either the solver (resp. symbol manager)
 * has its logic set, then the symbol manager (resp. solver) is set to use that
 * logic, if its logic is not already set.
 */
typedef struct Cvc5InputParser Cvc5InputParser;

/* -------------------------------------------------------------------------- */

/**
 * Construct a new instance of a cvc5 symbol manager.
 * @param tm The associated term manager instance.
 * @return The cvc5 symbol manager instance.
 */
CVC5_EXPORT Cvc5SymbolManager* cvc5_symbol_manager_new(Cvc5TermManager* tm);

/**
 * Delete a cvc5 symbol manager instance.
 * @param sm The symbol manager instance.
 */
CVC5_EXPORT void cvc5_symbol_manager_delete(Cvc5SymbolManager* sm);

/**
 * Determine if the logic of a given symbol manager has been set.
 * @param sm The symbol manager instance.
 * @return True if the logic has been set.
 */
CVC5_EXPORT bool cvc5_sm_is_logic_set(Cvc5SymbolManager* sm);

/**
 * Get the logic configured for a given symbol manager.
 * @note Asserts `cvc5_sm_is_logic_set()`.
 * @param sm The symbol manager instance.
 * @return The configured logic.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_sm_get_logic(Cvc5SymbolManager* sm);

/**
 * Get the list of sorts that have been declared via `declare-sort` commands.
 * These are the sorts that are printed as part of a response to a
 * `get-model` command.
 *
 * @param sm   The symbol manager instance.
 * @param size The size of the resulting sorts array.
 * @return The declared sorts.
 */
CVC5_EXPORT const Cvc5Sort* cvc5_sm_get_declared_sorts(Cvc5SymbolManager* sm,
                                                       size_t* size);

/**
 * Get the list of terms that have been declared via `declare-fun` and
 * `declare-const`. These are the terms that are printed in response to a
 * `get-model` command.
 *
 * @param sm   The symbol manager instance.
 * @param size The size of the resulting sorts array.
 * @return The declared terms.terms
 */
CVC5_EXPORT const Cvc5Term* cvc5_sm_get_declared_terms(Cvc5SymbolManager* sm,
                                                       size_t* size);

/* -------------------------------------------------------------------------- */

/**
 * Invoke a given command on the solver and symbol manager sm and return any
 * resulting output as a string.
 * @param cmd        The command to invoke.
 * @param solver     The solver to invoke the command on.
 * @param sm         The symbol manager to invoke the command on.
 * @return The output of invoking the command.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_cmd_invoke(Cvc5Command cmd,
                                        Cvc5* cvc5,
                                        Cvc5SymbolManager* sm);

/**
 * Get a string representation of this command.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_cmd_to_string(const Cvc5Command cmd);

/**
 * Get the name for a given command, e.g., "assert".
 * @return The name of the command.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_cmd_get_name(const Cvc5Command cmd);

/* -------------------------------------------------------------------------- */

/**
 * Construct a new instance of a cvc5 input parser.
 * @param cvc5 The associated solver instance.
 * @param sm   The associated symbol manager instance, contains a symbol table
 *             that maps symbols to terms and sorts. Must have a logic that is
 *             compatible with the solver. May be NULL to start with and
 *             initially empty symbol manager.
 * @return The cvc5 symbol manager instance.
 */
CVC5_EXPORT Cvc5InputParser* cvc5_parser_new(Cvc5* cvc5, Cvc5SymbolManager* sm);

/**
 * Delete a cvc5 input parser instance.
 * @param parser The input parser instance.
 */
CVC5_EXPORT void cvc5_parser_delete(Cvc5InputParser* parser);

/**
 * Release all objects managed by the parser.
 *
 * This will free all memory used by any managed objects allocated by the
 * parser.
 *
 * @note This invalidates all managed objects created by the parser.
 *
 * @param parser The parser instance.
 */
CVC5_EXPORT void cvc5_parser_release(Cvc5InputParser* parser);

/**
 * Get the associated solver instance of a given parser.
 * @param parser The parser instance.
 * @return The solver.
 */
Cvc5* cvc5_parser_get_solver(Cvc5InputParser* parser);

/**
 * Get the associated symbol manager of a given parser.
 * @param parser The parser instance.
 * @return The symbol manager.
 */
CVC5_EXPORT Cvc5SymbolManager* cvc5_parser_get_sm(Cvc5InputParser* parser);

/**
 * Configure given file as input to a given input parser.
 * @param parser The input parser instance.
 * @param lang the input language (e.g., #CVC5_INPUT_LANGUAGESMT_LIB_2_6)
 * @param filename The name of the file to configure.
 */
CVC5_EXPORT void cvc5_parser_set_file_input(Cvc5InputParser* parser,
                                            Cvc5InputLanguage lang,
                                            const char* filename);
/**
 * Configure a given concrete input string as the input to a given input parser.
 * @param parser The input parser instance.
 * @param lang  The input language of the input string.
 * @param input The input string.
 * @param name  The name to use as input stream name for error messages.
 */
CVC5_EXPORT void cvc5_parser_set_str_input(Cvc5InputParser* parser,
                                           Cvc5InputLanguage lang,
                                           const char* input,
                                           const char* name);
/**
 * Configure that we will be feeding strings to a given input parser via
 * `cvc5_parser_append_inc_str_input()` below.
 * @param parser The input parser instance.
 * @param lang  The input language of the input string.
 * @param name  The name to use as input stream name for error messages.
 */
CVC5_EXPORT void cvc5_parser_set_inc_str_input(Cvc5InputParser* parser,
                                               Cvc5InputLanguage lang,
                                               const char* name);
/**
 * Append string to the input being parsed by this parser. Should be
 * called after calling `cvc5_set_inc_str_input()`.
 * @param parser The input parser instance.
 * @param input  The input string.
 */
CVC5_EXPORT void cvc5_parser_append_inc_str_input(Cvc5InputParser* parser,
                                                  const char* input);

/**
 * Parse and return the next command. Will initialize the logic to "ALL"
 * or the forced logic if no logic is set prior to this point and a command
 * is read that requires initializing the logic.
 *
 * @param parser     The input parser instance.
 * @param error_msg  Output parameter for the error message in case of a parse
 *                   error, NULL if no error occurred.
 * @return The parsed command. NULL if no command was read.
 */
CVC5_EXPORT Cvc5Command cvc5_parser_next_command(Cvc5InputParser* parser,
                                                 const char** error_msg);

/**
 * Parse and return the next term. Requires setting the logic prior
 * to this point.
 * @param parser     The input parser instance.
 * @param error_msg  Output parameter for the error message in case of a parse
 *                   error, NULL if no error occurred.
 * @return           The parsed term. NULL if no term was read.
 */
CVC5_EXPORT Cvc5Term cvc5_parser_next_term(Cvc5InputParser* parser,
                                           const char** error_msg);

/**
 * Is this parser done reading input?
 * @param parser The input parser instance.
 * @return True if parser is done reading input.
 */
CVC5_EXPORT bool cvc5_parser_done(Cvc5InputParser* parser);

#if __cplusplus
}
#endif
#endif
