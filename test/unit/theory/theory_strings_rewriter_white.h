/*********************                                                        */
/*! \file theory_strings_rewriter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for the strings rewriter
 **
 ** Unit tests for the strings rewriter.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"

#include <cxxtest/TestSuite.h>
#include <vector>

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

class TheoryStringsRewriterWhite : public CxxTest::TestSuite
{
  ExprManager *d_em;
  NodeManager *d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;

 public:
  TheoryStringsRewriterWhite() {}

  void setUp()
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager(opts);
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);
  }

  void tearDown()
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testCheckEqAndEntailArithUnsat()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node x = d_nm->mkVar("x", intType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", intType);

    Node slen_y = d_nm->mkNode(kind::STRING_LENGTH, y);
    Node x_plus_slen_y = d_nm->mkNode(kind::PLUS, x, slen_y);
    Node x_plus_slen_y_eq_zero = Rewriter::rewrite(
        d_nm->mkNode(kind::EQUAL, x_plus_slen_y, d_nm->mkConst(Rational(0))));

    // x + (str.len y) = 0 /\ x > 0 --> true
    TS_ASSERT(TheoryStringsRewriter::checkEqAndEntailArithUnsat(
        x_plus_slen_y_eq_zero, x, true));

    // x + (str.len y) = 0 /\ x >= 0 --> false
    TS_ASSERT(!TheoryStringsRewriter::checkEqAndEntailArithUnsat(
        x_plus_slen_y_eq_zero, x, false));

    Node x_plus_slen_y_plus_z_eq_zero = Rewriter::rewrite(
        d_nm->mkNode(kind::EQUAL,
                     d_nm->mkNode(kind::PLUS, x_plus_slen_y, z),
                     d_nm->mkConst(Rational(0))));

    // x + (str.len y) + z = 0 /\ x > 0 --> false
    TS_ASSERT(!TheoryStringsRewriter::checkEqAndEntailArithUnsat(
        x_plus_slen_y_plus_z_eq_zero, x, true));

    Node x_plus_slen_y_plus_slen_y_eq_zero = Rewriter::rewrite(
        d_nm->mkNode(kind::EQUAL,
                     d_nm->mkNode(kind::PLUS, x_plus_slen_y, slen_y),
                     d_nm->mkConst(Rational(0))));

    // x + (str.len y) + (str.len y) = 0 /\ x > 0 --> true
    TS_ASSERT(TheoryStringsRewriter::checkEqAndEntailArithUnsat(
        x_plus_slen_y_plus_slen_y_eq_zero, x, true));
  }

  void testRewriteSubstr()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node s = d_nm->mkVar("s", strType);
    Node x = d_nm->mkVar("x", intType);
    Node y = d_nm->mkVar("y", intType);

    // (str.substr "A" x x) --> ""
    Node n = d_nm->mkNode(kind::STRING_SUBSTR, a, x, x);
    Node res = TheoryStringsRewriter::rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "A" (+ x 1) x) -> ""
    n = d_nm->mkNode(kind::STRING_SUBSTR,
                     a,
                     d_nm->mkNode(kind::PLUS, x, d_nm->mkConst(Rational(1))),
                     x);
    res = TheoryStringsRewriter::rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "A" (+ x (str.len s2)) x) -> ""
    n = d_nm->mkNode(
        kind::STRING_SUBSTR,
        a,
        d_nm->mkNode(kind::PLUS, x, d_nm->mkNode(kind::STRING_LENGTH, s)),
        x);
    res = TheoryStringsRewriter::rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "A" x y) -> (str.substr "A" x y)
    n = d_nm->mkNode(kind::STRING_SUBSTR, a, x, y);
    res = TheoryStringsRewriter::rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, n);
  }
};
