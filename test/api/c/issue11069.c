/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #11069.
 */

#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>

#include <iostream>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5Solver* slv = cvc5_new(d_tm);

  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(d_tm);

  cvc5_set_logic(slv, "QF_BV");

  // construct an input parser associated the solver above
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, d_sm);

  std::string input1("(declare-const x (_ BitVec 4))\n(assert (= x #b0001))\n");
  cvc5_parser_set_inc_str_input(
          parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "myInput");
  cvc5_parser_append_inc_str_input(parser, input1.c_str());

  // parse commands until finished
  Cvc5Command cmd;
  while (true)
  {
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser, &error_msg);
    if (cmd.isNull())
    {
      break;
    }
    (void)cvc5_cmd_invoke(cmd, &slv, &sm);
  }
  Cvc5Result result = cvc5_check_sat(d_solver);
  std::cout << "Result:" << result << std::endl;

  std::string input2("(assert (= x #b0101))");
  cvc5_parser_append_inc_str_input(parser, input2.c_str());
  const char* error_msg;
  cmd = cvc5_parser_next_command(parser, &error_msg);
  assert(!cmd.isNull());
  (void)cvc5_cmd_invoke(cmd, &slv, &sm);
  result = cvc5_check_sat(d_solver);
  std::cout << "Result:" << result << std::endl;
  assert(cvc5_result_is_unsat(result));
  return 0;
}
