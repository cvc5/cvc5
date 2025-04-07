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
 * A simple demonstration of using the parser via the C API.
 */

#include <assert.h>
#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  // set that we should print success after each successful command
  cvc5_set_option(slv, "print-success", "true");

  // construct an input parser associated the solver above
  Cvc5InputParser* parser = cvc5_parser_new(slv, NULL);
  cvc5_parser_set_str_input(
      parser,
      CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
      "(set-logic QF_LIA)\n(declare-fun a () Int)\n(declare-fun b () "
      "Int)\n(declare-fun c () Int)\n(assert (> a (+ b c)))\n(assert (< a "
      "b))\n(assert (> c 0))\n",
      "foo");

  // get the symbol manager of the parser, used when invoking commands below
  Cvc5SymbolManager* sm = cvc5_parser_get_sm(parser);

  // parse commands until finished
  Cvc5Command cmd;
  do
  {
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser, &error_msg);
    assert(error_msg == NULL);
    if (cmd)
    {
      printf("Executing command %s:\n", cvc5_cmd_to_string(cmd));
      // invoke the command on the solver and the symbol manager, print the
      // result to stdout
      printf("%s", cvc5_cmd_invoke(cmd, slv, sm));
    }
  } while (cmd);
  printf("Finished parsing commands\n");

  // now, check sat with the solver
  Cvc5Result r = cvc5_check_sat(slv);
  printf("expected: unsat\n");
  printf("result: %s\n", cvc5_result_to_string(r));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
