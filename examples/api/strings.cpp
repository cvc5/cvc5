/*********************                                                        */
/*! \file strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reasoning about strings with CVC4 via C++ API.
 **
 ** A simple demonstration of reasoning about strings with CVC4 via C++ API.
 **/

#include <iostream>

#include <cvc4/cvc4.h>
#include <cvc4/options/set_language.h>

using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);

  // Set the logic
  smt.setLogic("S");

  // Produce models
  smt.setOption("produce-models", true);

  // The option strings-exp is needed
  smt.setOption("strings-exp", true);

  // Set output language to SMTLIB2
  std::cout << language::SetLanguage(language::output::LANG_SMTLIB_V2);

  // String type
  Type string = em.stringType();

  // std::string
  std::string std_str_ab("ab");
  // CVC4::String
  CVC4::String cvc4_str_ab(std_str_ab);
  CVC4::String cvc4_str_abc("abc");
  // String constants
  Expr ab  = em.mkConst(cvc4_str_ab);
  Expr abc = em.mkConst(CVC4::String("abc"));
  // String variables
  Expr x = em.mkVar("x", string);
  Expr y = em.mkVar("y", string);
  Expr z = em.mkVar("z", string);

  // String concatenation: x.ab.y
  Expr lhs = em.mkExpr(kind::STRING_CONCAT, x, ab, y);
  // String concatenation: abc.z
  Expr rhs = em.mkExpr(kind::STRING_CONCAT, abc, z);
  // x.ab.y = abc.z
  Expr formula1 = em.mkExpr(kind::EQUAL, lhs, rhs);

  // Length of y: |y|
  Expr leny = em.mkExpr(kind::STRING_LENGTH, y);
  // |y| >= 0
  Expr formula2 = em.mkExpr(kind::GEQ, leny, em.mkConst(Rational(0)));

  // Regular expression: (ab[c-e]*f)|g|h
  Expr r = em.mkExpr(kind::REGEXP_UNION,
    em.mkExpr(kind::REGEXP_CONCAT,
      em.mkExpr(kind::STRING_TO_REGEXP, em.mkConst(String("ab"))),
      em.mkExpr(kind::REGEXP_STAR,
        em.mkExpr(kind::REGEXP_RANGE, em.mkConst(String("c")), em.mkConst(String("e")))),
      em.mkExpr(kind::STRING_TO_REGEXP, em.mkConst(String("f")))),
    em.mkExpr(kind::STRING_TO_REGEXP, em.mkConst(String("g"))),
    em.mkExpr(kind::STRING_TO_REGEXP, em.mkConst(String("h"))));

  // String variables
  Expr s1 = em.mkVar("s1", string);
  Expr s2 = em.mkVar("s2", string);
  // String concatenation: s1.s2
  Expr s = em.mkExpr(kind::STRING_CONCAT, s1, s2);

  // s1.s2 in (ab[c-e]*f)|g|h
  Expr formula3 = em.mkExpr(kind::STRING_IN_REGEXP, s, r);

  // Make a query
  Expr q = em.mkExpr(kind::AND,
    formula1,
    formula2,
    formula3);

  // check sat
  Result result = smt.checkSat(q);
  std::cout << "CVC4 reports: " << q << " is " << result << "." << std::endl;

  if(result == Result::SAT) {
    std::cout << "  x  = " << smt.getValue(x) << std::endl;
    std::cout << "  s1.s2 = " << smt.getValue(s) << std::endl;
  }
}
