/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
 * To add a new test, simply add a call to runTestString() under
 * runTest(), below.  If you don't specify an input language,
 * LANG_SMTLIB_V2 is used.  If your example depends on variables,
 * you'll need to declare them in the "declarations" global, just
 * below, in SMT-LIBv2 form (but they're good for all languages).
 */

#include <cassert>
#include <iostream>
#include <string>

#include "api/cpp/cvc5.h"
#include "options/set_language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"

using namespace cvc5;
using namespace cvc5::parser;
using namespace cvc5::language;

int runTest();

int main()
{
  try
  {
    return runTest();
  }
  catch (api::CVC5ApiException& e)
  {
    std::cerr << e.getMessage() << std::endl;
  }
  catch (parser::ParserException& e)
  {
    std::cerr << e.getMessage() << std::endl;
  }
  catch (...)
  {
    std::cerr << "non-cvc5 exception thrown" << std::endl;
  }
  return 1;
}

std::string parse(std::string instr,
                  std::string input_language,
                  std::string output_language)
{
  assert(input_language == "smt2" || input_language == "cvc");
  assert(output_language == "smt2" || output_language == "cvc");

  std::string declarations;

  if (input_language == "smt2")
  {
    declarations =
        "\
  (declare-sort U 0)\n\
  (declare-fun f (U) U)\n\
  (declare-fun x () U)\n\
  (declare-fun y () U)\n\
  (assert (= (f x) x))\n\
  (declare-fun a () (Array U (Array U U)))\n\
  ";
  }
  else
  {
    declarations =
        "\
      U: TYPE;\n\
      f: U -> U;\n\
      x,y: U;\n\
      a: ARRAY U OF (ARRAY U OF U);\n\
      ASSERT f(x) = x;\n\
  ";
  }

  api::Solver solver;
  std::string ilang =
      input_language == "smt2" ? "LANG_SMTLIB_V2_6" : "LANG_CVC";

  solver.setOption("input-language", input_language);
  solver.setOption("output-language", output_language);
  SymbolManager symman(&solver);
  std::unique_ptr<Parser> parser(
      ParserBuilder(&solver, &symman, false)
          .withInputLanguage(solver.getOption("input-language"))
          .build());
  parser->setInput(
      Input::newStringInput(ilang, declarations, "internal-buffer"));
  // we don't need to execute the commands, but we DO need to parse them to
  // get the declarations
  while (Command* c = parser->nextCommand())
  {
    delete c;
  }
  assert(parser->done());  // parser should be done
  parser->setInput(Input::newStringInput(ilang, instr, "internal-buffer"));
  api::Term e = parser->nextExpression();
  std::string s = e.toString();
  assert(parser->nextExpression().isNull());  // next expr should be null
  return s;
}

std::string translate(std::string instr,
                      std::string input_language,
                      std::string output_language)
{
  assert(input_language == "smt2" || input_language == "cvc");
  assert(output_language == "smt2" || output_language == "cvc");

  std::cout << "==============================================" << std::endl
            << "translating from "
            << (input_language == "smt2" ? Language::LANG_SMTLIB_V2_6
                                         : Language::LANG_CVC)
            << " to "
            << (output_language == "smt2" ? Language::LANG_SMTLIB_V2_6
                                          : Language::LANG_CVC)
            << " this string:" << std::endl
            << instr << std::endl;
  std::string outstr = parse(instr, input_language, output_language);
  std::cout << "got this:" << std::endl
            << outstr << std::endl
            << "reparsing as "
            << (output_language == "smt2" ? Language::LANG_SMTLIB_V2_6
                                          : Language::LANG_CVC)
            << std::endl;
  std::string poutstr = parse(outstr, output_language, output_language);
  assert(outstr == poutstr);
  std::cout << "got same expressions " << outstr << " and " << poutstr
            << std::endl
            << "==============================================" << std::endl;
  return outstr;
}

void runTestString(std::string instr, std::string instr_language)
{
  std::cout << std::endl
            << "starting with: " << instr << std::endl
            << "   in language " << Language::LANG_SMTLIB_V2_6 << std::endl;
  std::string smt2str = translate(instr, instr_language, "smt2");
  std::cout << "in SMT2      : " << smt2str << std::endl;
  std::string cvcstr = translate(smt2str, "smt2", "cvc");
  std::cout << "in CVC       : " << cvcstr << std::endl;
  std::string outstr = translate(cvcstr, "cvc", "smt2");
  std::cout << "back to SMT2 : " << outstr << std::endl << std::endl;

  assert(outstr == smt2str);  // differences in output
}

int32_t runTest()
{
  runTestString("(= (f (f y)) x)", "smt2");
  runTestString("~BVPLUS(3, 0bin00, 0bin11)[2:1] = 0bin10", "cvc");
  runTestString("~BVPLUS(3, BVMULT(2, 0bin01, 0bin11), 0bin11)[2:0]", "cvc");
  runTestString("a[x][y] = a[y][x]", "cvc");
  return 0;
}
