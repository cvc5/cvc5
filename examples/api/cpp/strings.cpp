/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tianyi Liang, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about strings via the C++ API.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);

  // Set the logic
  slv.setLogic("QF_SLIA");
  // Produce models
  slv.setOption("produce-models", "true");
  // The option strings-exp is needed
  slv.setOption("strings-exp", "true");

  // String type
  Sort string = tm.getStringSort();

  // std::string
  std::string str_ab("ab");
  // String constants
  Term ab = tm.mkString(str_ab);
  Term abc = tm.mkString("abc");
  // String variables
  Term x = tm.mkConst(string, "x");
  Term y = tm.mkConst(string, "y");
  Term z = tm.mkConst(string, "z");

  // String concatenation: x.ab.y
  Term lhs = tm.mkTerm(Kind::STRING_CONCAT, {x, ab, y});
  // String concatenation: abc.z
  Term rhs = tm.mkTerm(Kind::STRING_CONCAT, {abc, z});
  // x.ab.y = abc.z
  Term formula1 = tm.mkTerm(Kind::EQUAL, {lhs, rhs});

  // Length of y: |y|
  Term leny = tm.mkTerm(Kind::STRING_LENGTH, {y});
  // |y| >= 0
  Term formula2 = tm.mkTerm(Kind::GEQ, {leny, tm.mkInteger(0)});

  // Regular expression: (ab[c-e]*f)|g|h
  Term r = tm.mkTerm(
      Kind::REGEXP_UNION,

      {tm.mkTerm(Kind::REGEXP_CONCAT,
                 {tm.mkTerm(Kind::STRING_TO_REGEXP, {tm.mkString("ab")}),
                  tm.mkTerm(Kind::REGEXP_STAR,
                            {tm.mkTerm(Kind::REGEXP_RANGE,
                                       {tm.mkString("c"), tm.mkString("e")})}),
                  tm.mkTerm(Kind::STRING_TO_REGEXP, {tm.mkString("f")})}),
       tm.mkTerm(Kind::STRING_TO_REGEXP, {tm.mkString("g")}),
       tm.mkTerm(Kind::STRING_TO_REGEXP, {tm.mkString("h")})});

  // String variables
  Term s1 = tm.mkConst(string, "s1");
  Term s2 = tm.mkConst(string, "s2");
  // String concatenation: s1.s2
  Term s = tm.mkTerm(Kind::STRING_CONCAT, {s1, s2});

  // s1.s2 in (ab[c-e]*f)|g|h
  Term formula3 = tm.mkTerm(Kind::STRING_IN_REGEXP, {s, r});

  // Make a query
  Term q = tm.mkTerm(Kind::AND, {formula1, formula2, formula3});

  // check sat
  Result result = slv.checkSatAssuming(q);
  std::cout << "cvc5 reports: " << q << " is " << result << "." << std::endl;

  if(result.isSat())
  {
    std::cout << "  x  = " << slv.getValue(x) << std::endl;
    std::cout << "  s1.s2 = " << slv.getValue(s) << std::endl;
  }
}
