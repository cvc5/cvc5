/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #11069.
 */

#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>

#include <stdio.h>
#include <assert.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(tm);

  cvc5_set_logic(slv, "QF_BV");

  // construct an input parser associated the solver above
  Cvc5InputParser* parser = cvc5_parser_new(slv, sm);

  const char* input1 = "(declare-const x (_ BitVec 4))\n(assert (= x #b0001))\n";
  cvc5_parser_set_inc_str_input(
          parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "myInput");
  cvc5_parser_append_inc_str_input(parser, input1);

  // parse commands until finished
  Cvc5Command cmd;
  while (true)
  {
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser, &error_msg);
    if (cmd == NULL)
    {
      break;
    }
    (void)cvc5_cmd_invoke(cmd, slv, sm);
  }
  Cvc5Result result = cvc5_check_sat(slv);
  printf("Result: %s\n", cvc5_result_to_string(result));

  const char* input2 = "(assert (= x #b0101))";
  cvc5_parser_append_inc_str_input(parser, input2);
  const char* error_msg;
  cmd = cvc5_parser_next_command(parser, &error_msg);
  assert(cmd != NULL);
  (void)cvc5_cmd_invoke(cmd, slv, sm);
  result = cvc5_check_sat(slv);
  printf("Result: %s\n", cvc5_result_to_string(result));
  assert(cvc5_result_is_unsat(result));

  cvc5_parser_delete(parser);
  cvc5_symbol_manager_delete(sm);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);

  return 0;
}
