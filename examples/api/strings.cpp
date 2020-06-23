/*********************                                                        */
/*! \file strings-new.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reasoning about strings with CVC4 via C++ API.
 **
 ** A simple demonstration of reasoning about strings with CVC4 via C++ API.
 **/

#include <iostream>

#include <cvc4/api/cvc4cpp.h>

using namespace CVC4::api;

int main()
{
  Solver slv;

  // Set the logic
  slv.setLogic("S");
  // Produce models
  slv.setOption("produce-models", "true");
  // The option strings-exp is needed
  slv.setOption("strings-exp", "true");
  // Set output language to SMTLIB2
  slv.setOption("output-language", "smt2");

  // String type
  Sort string = slv.getStringSort();

  // std::string
  std::string str_ab("ab");
  // String constants
  Term ab  = slv.mkString(str_ab);
  Term abc = slv.mkString("abc");
  // String variables
  Term x = slv.mkConst(string, "x");
  Term y = slv.mkConst(string, "y");
  Term z = slv.mkConst(string, "z");

  // String concatenation: x.ab.y
  Term lhs = slv.mkTerm(STRING_CONCAT, x, ab, y);
  // String concatenation: abc.z
  Term rhs = slv.mkTerm(STRING_CONCAT, abc, z);
  // x.ab.y = abc.z
  Term formula1 = slv.mkTerm(EQUAL, lhs, rhs);

  // Length of y: |y|
  Term leny = slv.mkTerm(STRING_LENGTH, y);
  // |y| >= 0
  Term formula2 = slv.mkTerm(GEQ, leny, slv.mkReal(0));

  // Regular expression: (ab[c-e]*f)|g|h
  Term r = slv.mkTerm(REGEXP_UNION,
    slv.mkTerm(REGEXP_CONCAT,
      slv.mkTerm(STRING_TO_REGEXP, slv.mkString("ab")),
      slv.mkTerm(REGEXP_STAR,
        slv.mkTerm(REGEXP_RANGE, slv.mkString("c"), slv.mkString("e"))),
      slv.mkTerm(STRING_TO_REGEXP, slv.mkString("f"))),
    slv.mkTerm(STRING_TO_REGEXP, slv.mkString("g")),
    slv.mkTerm(STRING_TO_REGEXP, slv.mkString("h")));

  // String variables
  Term s1 = slv.mkConst(string, "s1");
  Term s2 = slv.mkConst(string, "s2");
  // String concatenation: s1.s2
  Term s = slv.mkTerm(STRING_CONCAT, s1, s2);

  // s1.s2 in (ab[c-e]*f)|g|h
  Term formula3 = slv.mkTerm(STRING_IN_REGEXP, s, r);

  // Make a query
  Term q = slv.mkTerm(AND,
    formula1,
    formula2,
    formula3);

  // check sat
  Result result = slv.checkSatAssuming(q);
  std::cout << "CVC4 reports: " << q << " is " << result << "." << std::endl;

  if(result.isSat())
  {
    std::cout << "  x  = " << slv.getValue(x) << std::endl;
    std::cout << "  s1.s2 = " << slv.getValue(s) << std::endl;
  }
}
