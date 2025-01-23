/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of using multiple parsers with the same symbol manager
 * via the C API.
 */

#include <assert.h>
#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(tm);

  // construct an input parser associated the solver above
  Cvc5InputParser* parser1 = cvc5_parser_new(slv, sm);

  cvc5_parser_set_str_input(
      parser1,
      CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
      "(set-logic QF_LIA)\n(declare-fun a () Int)\n(declare-fun b () "
      "Int)\n(declare-fun c () Bool)\n",
      "foo");

  // parse commands until finished
  Cvc5Command cmd;
  do
  {
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser1, &error_msg);
    if (cmd)
    {
      printf("Executing command %s:\n", cvc5_cmd_to_string(cmd));
      // invoke the command on the solver and the symbol manager, print the
      // result to stdout
      printf("%s", cvc5_cmd_invoke(cmd, slv, sm));
    }
  } while (cmd);
  printf("Finished parsing commands\n");

  // Note that sm now has a,b,c in its symbol table.

  // Now, construct a new parser with the same symbol manager. We will parse
  // terms with it.
  Cvc5InputParser* parser2 = cvc5_parser_new(slv, sm);
  cvc5_parser_set_str_input(parser2,
                            CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
                            "(+ a b)\n(- a 10)\n(>= 0 45)\n(and c c)\ntrue\n",
                            "bar");

  // parse terms until finished
  Cvc5Term t = NULL;
  do
  {
    const char* error_msg;
    t = cvc5_parser_next_term(parser2, &error_msg);
    assert(error_msg == NULL);
    printf("Parsed term: %s\n", t ? cvc5_term_to_string(t) : "null");
  } while (t);
  printf("Finished parsing terms\n");

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
