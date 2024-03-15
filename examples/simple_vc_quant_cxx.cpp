/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the C++ interface for quantifiers.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);

  // Prove that the following is unsatisfiable:
  //   forall x. P( x ) ^ ~P( 5 )

  Sort integer = tm.getIntegerSort();
  Sort boolean = tm.getBooleanSort();
  Sort integerPredicate = tm.mkFunctionSort({integer}, boolean);

  Term p = tm.mkConst(integerPredicate, "P");
  Term x = tm.mkVar(integer, "x");

  // make forall x. P( x )
  Term var_list = tm.mkTerm(Kind::VARIABLE_LIST, {x});
  Term px = tm.mkTerm(Kind::APPLY_UF, {p, x});
  Term quantpospx = tm.mkTerm(Kind::FORALL, {var_list, px});
  std::cout << "Made expression : " << quantpospx << std::endl;

  //make ~P( 5 )
  Term five = tm.mkInteger(5);
  Term pfive = tm.mkTerm(Kind::APPLY_UF, {p, five});
  Term negpfive = tm.mkTerm(Kind::NOT, {pfive});
  std::cout << "Made expression : " << negpfive << std::endl;

  Term formula = tm.mkTerm(Kind::AND, {quantpospx, negpfive});

  slv.assertFormula(formula);

  std::cout << "Checking SAT after asserting " << formula << " to cvc5."
            << std::endl;
  std::cout << "cvc5 should report unsat." << std::endl;
  std::cout << "Result from cvc5 is: " << slv.checkSat() << std::endl;

  slv.resetAssertions();

  // this version has a pattern e.g. in smt2 syntax (forall ((x Int)) (! (P x ) :pattern ((P x))))
  Term pattern = tm.mkTerm(Kind::INST_PATTERN, {px});
  Term pattern_list = tm.mkTerm(Kind::INST_PATTERN_LIST, {pattern});
  Term quantpospx_pattern =
      tm.mkTerm(Kind::FORALL, {var_list, px, pattern_list});
  std::cout << "Made expression : " << quantpospx_pattern << std::endl;

  Term formula_pattern = tm.mkTerm(Kind::AND, {quantpospx_pattern, negpfive});

  slv.assertFormula(formula_pattern);

  std::cout << "Checking SAT after asserting " << formula_pattern << " to cvc5."
            << std::endl;
  std::cout << "cvc5 should report unsat." << std::endl;
  std::cout << "Result from cvc5 is: " << slv.checkSat() << std::endl;

  return 0;
}
