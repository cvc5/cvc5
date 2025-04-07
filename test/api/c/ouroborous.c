/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * "Ouroborous" test: does cvc5 read its own output?
 *
 * The "Ouroborous" test, named after the serpent that swallows its
 * own tail, ensures that cvc5 can parse some input, output it again
 * (in any of its languages) and then parse it again.  The result of
 * the first parse must be equal to the result of the second parse;
 * both strings and expressions are compared for equality.
 *
 * To add a new test, simply add a call to run_test_string() under
 * run_test(), below.  If you don't specify an input language,
 * LANG_SMTLIB_V2 is used.  If your example depends on symbolic constants,
 * you'll need to declare them in the "declarations" global, just
 * below, in SMT-LIBv2 form (but they're good for all languages).
 */

#include <assert.h>
#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

char* parse(const char* instr, const char* inlang, const char* outlang)
{
  assert(strcmp(inlang, "smt2") == 0);
  assert(strcmp(outlang, "smt2") == 0);

  const char* declarations =
      "(set-logic ALL)\n"
      "(declare-sort U 0)\n"
      "(declare-fun f (U) U)\n"
      "(declare-fun x () U)\n"
      "(declare-fun y () U)\n"
      "(assert (= (f x) x))\n"
      "(declare-fun a () (Array U (Array U U)))\n";

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* solver = cvc5_new(tm);

  cvc5_set_option(solver, "input-language", inlang);
  cvc5_set_option(solver, "output-language", outlang);

  Cvc5SymbolManager* smgr = cvc5_symbol_manager_new(tm);
  Cvc5InputParser* parser = cvc5_parser_new(solver, smgr);
  cvc5_parser_set_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, declarations, "ouroborous");

  // we don't need to execute the commands, but we DO need to parse them to
  // get the declarations
  Cvc5Command cmd;
  do
  {
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser, &error_msg);
    assert(error_msg == NULL);
    if (cmd)
    {
      cvc5_cmd_invoke(cmd, solver, smgr);
    }
  } while (cmd);
  assert(cvc5_parser_done(parser));  // parser should be done
  cvc5_parser_set_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, instr, "ouroborous");
  const char* error_msg;
  Cvc5Term e = cvc5_parser_next_term(parser, &error_msg);
  assert(!error_msg);
  char* s = strdup(cvc5_term_to_string(e));
  assert(!cvc5_parser_next_term(parser, &error_msg));
  assert(!error_msg);
  cvc5_parser_delete(parser);
  cvc5_symbol_manager_delete(smgr);
  cvc5_delete(solver);
  cvc5_term_manager_delete(tm);
  return s;
}

char* translate(const char* str, const char* inlang, const char* outlang)
{
  assert(strcmp(inlang, "smt2") == 0);
  assert(strcmp(outlang, "smt2") == 0);

  printf("==============================================\n");
  printf("translating from %s to %s this string:\n%s\n", inlang, outlang, str);
  char* outstr = parse(str, inlang, outlang);
  printf("got this:\n%s\n", outstr);
  printf("reparsing as %s\n", outlang);
  char* poutstr = parse(outstr, outlang, outlang);
  assert(strcmp(outstr, poutstr) == 0);
  printf("got same expressions %s and %s\n", outstr, poutstr);
  printf("==============================================\n");
  free(poutstr);
  return outstr;
}

void run_test_string(const char* str, const char* lang)
{
  printf("\n");
  printf("starting with: %s\n", str);
  printf("   in language %s\n", lang);
  char* smt2str = translate(str, lang, "smt2");
  printf("in SMT2      : %s\n", smt2str);
  char* outstr = translate(smt2str, "smt2", "smt2");
  printf("to SMT2 : %s\n\n", outstr);

  assert(strcmp(outstr, smt2str) == 0);  // differences in output
  free(smt2str);
  free(outstr);
}

int main()
{
  run_test_string("(= (f (f y)) x)", "smt2");
  run_test_string("(= ((_ extract 2 1) (bvnot (bvadd #b000 #b011))) #b10)",
                  "smt2");
  run_test_string("((_ extract 2 0) (bvnot (bvadd (bvmul #b001 #b011) #b011)))",
                  "smt2");
  return 0;
}
