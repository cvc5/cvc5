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
 * A test of SMT-LIBv2 commands, checks for compliant output.
 */

#include <assert.h>
#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_get_info(Cvc5* solver, const char* s)
{
  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(cvc5_get_tm(solver));
  Cvc5InputParser* parser = cvc5_parser_new(solver, sm);

  char* str = malloc((strlen(s) + strlen("(get-info )") + 1) * sizeof(char));
  sprintf(str, "(get-info %s)", s);
  cvc5_parser_set_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, str, "<internal>");
  Cvc5Command cmd;
  do
  {
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser, &error_msg);
    assert(error_msg == NULL);
    if (cmd)
    {
      printf("%s", cvc5_cmd_invoke(cmd, solver, sm));
    }
  } while (cmd);
  assert(cvc5_parser_done(parser));  // parser should be done
  cvc5_parser_delete(parser);
  cvc5_symbol_manager_delete(sm);
  free(str);
}

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* solver = cvc5_new(tm);
  cvc5_set_option(solver, "input-language", "smtlib2");
  cvc5_set_option(solver, "output-language", "smtlib2");
  test_get_info(solver, ":error-behavior");
  test_get_info(solver, ":name");
  test_get_info(solver, ":authors");
  test_get_info(solver, ":version");
  test_get_info(solver, ":status");
  test_get_info(solver, ":reason-unknown");
  test_get_info(solver, ":arbitrary-undefined-keyword");
  test_get_info(solver, ":<=");  // legal
  test_get_info(solver, ":->");  // legal
  test_get_info(solver, ":all-statistics");

  cvc5_delete(solver);
  cvc5_term_manager_delete(tm);
  return 0;
}
