/*********************                                                        */
/*! \file sequences_rewriter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for the strings/sequences rewriter
 **
 ** Unit tests for the strings/sequences rewriter.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/strings_entail.h"
#include "theory/strings/strings_rewriter.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::strings;

class SequencesRewriterWhite : public CxxTest::TestSuite
{
 public:
  SequencesRewriterWhite() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager;
    d_smt = new SmtEngine(d_em, &opts);
    d_scope = new SmtScope(d_smt);
    d_smt->finishInit();
    d_rewriter = new ExtendedRewriter(true);

    d_nm = NodeManager::currentNM();
  }

  void tearDown() override
  {
    delete d_rewriter;
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void inNormalForm(Node t)
  {
    Node res_t = d_rewriter->extendedRewrite(t);

    std::cout << std::endl;
    std::cout << t << " ---> " << res_t << std::endl;
    TS_ASSERT_EQUALS(t, res_t);
  }

  void sameNormalForm(Node t1, Node t2)
  {
    Node res_t1 = d_rewriter->extendedRewrite(t1);
    Node res_t2 = d_rewriter->extendedRewrite(t2);

    std::cout << std::endl;
    std::cout << t1 << " ---> " << res_t1 << std::endl;
    std::cout << t2 << " ---> " << res_t2 << std::endl;
    TS_ASSERT_EQUALS(res_t1, res_t2);
  }

  void differentNormalForms(Node t1, Node t2)
  {
    Node res_t1 = d_rewriter->extendedRewrite(t1);
    Node res_t2 = d_rewriter->extendedRewrite(t2);

    std::cout << std::endl;
    std::cout << t1 << " ---> " << res_t1 << std::endl;
    std::cout << t2 << " ---> " << res_t2 << std::endl;
    TS_ASSERT_DIFFERS(res_t1, res_t2);
  }

  void testCheckEntailLengthOne()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node aaad = d_nm->mkConst(::CVC4::String("AAAD"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node negOne = d_nm->mkConst(Rational(-1));
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));
    Node i = d_nm->mkVar("i", intType);

    TS_ASSERT(StringsEntail::checkLengthOne(a));
    TS_ASSERT(StringsEntail::checkLengthOne(a, true));

    Node substr = d_nm->mkNode(kind::STRING_SUBSTR, x, zero, one);
    TS_ASSERT(StringsEntail::checkLengthOne(substr));
    TS_ASSERT(!StringsEntail::checkLengthOne(substr, true));

    substr = d_nm->mkNode(kind::STRING_SUBSTR,
                          d_nm->mkNode(kind::STRING_CONCAT, a, x),
                          zero,
                          one);
    TS_ASSERT(StringsEntail::checkLengthOne(substr));
    TS_ASSERT(StringsEntail::checkLengthOne(substr, true));

    substr = d_nm->mkNode(kind::STRING_SUBSTR, x, zero, two);
    TS_ASSERT(!StringsEntail::checkLengthOne(substr));
    TS_ASSERT(!StringsEntail::checkLengthOne(substr, true));
  }

  void testCheckEntailArith()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node z = d_nm->mkVar("z", strType);
    Node n = d_nm->mkVar("n", intType);
    Node one = d_nm->mkConst(Rational(1));

    // 1 >= (str.len (str.substr z n 1)) ---> true
    Node substr_z = d_nm->mkNode(kind::STRING_LENGTH,
                                 d_nm->mkNode(kind::STRING_SUBSTR, z, n, one));
    TS_ASSERT(ArithEntail::check(one, substr_z));

    // (str.len (str.substr z n 1)) >= 1 ---> false
    TS_ASSERT(!ArithEntail::check(substr_z, one));
  }

  void testCheckEntailArithWithAssumption()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node x = d_nm->mkVar("x", intType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", intType);

    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));

    Node slen_y = d_nm->mkNode(kind::STRING_LENGTH, y);
    Node x_plus_slen_y = d_nm->mkNode(kind::PLUS, x, slen_y);
    Node x_plus_slen_y_eq_zero =
        Rewriter::rewrite(d_nm->mkNode(kind::EQUAL, x_plus_slen_y, zero));

    // x + (str.len y) = 0 |= 0 >= x --> true
    TS_ASSERT(ArithEntail::checkWithAssumption(
        x_plus_slen_y_eq_zero, zero, x, false));

    // x + (str.len y) = 0 |= 0 > x --> false
    TS_ASSERT(!ArithEntail::checkWithAssumption(
        x_plus_slen_y_eq_zero, zero, x, true));

    Node x_plus_slen_y_plus_z_eq_zero = Rewriter::rewrite(d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::PLUS, x_plus_slen_y, z), zero));

    // x + (str.len y) + z = 0 |= 0 > x --> false
    TS_ASSERT(!ArithEntail::checkWithAssumption(
        x_plus_slen_y_plus_z_eq_zero, zero, x, true));

    Node x_plus_slen_y_plus_slen_y_eq_zero = Rewriter::rewrite(d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::PLUS, x_plus_slen_y, slen_y), zero));

    // x + (str.len y) + (str.len y) = 0 |= 0 >= x --> true
    TS_ASSERT(ArithEntail::checkWithAssumption(
        x_plus_slen_y_plus_slen_y_eq_zero, zero, x, false));

    Node five = d_nm->mkConst(Rational(5));
    Node six = d_nm->mkConst(Rational(6));
    Node x_plus_five = d_nm->mkNode(kind::PLUS, x, five);
    Node x_plus_five_lt_six =
        Rewriter::rewrite(d_nm->mkNode(kind::LT, x_plus_five, six));

    // x + 5 < 6 |= 0 >= x --> true
    TS_ASSERT(
        ArithEntail::checkWithAssumption(x_plus_five_lt_six, zero, x, false));

    // x + 5 < 6 |= 0 > x --> false
    TS_ASSERT(
        !ArithEntail::checkWithAssumption(x_plus_five_lt_six, zero, x, true));

    Node neg_x = d_nm->mkNode(kind::UMINUS, x);
    Node x_plus_five_lt_five =
        Rewriter::rewrite(d_nm->mkNode(kind::LT, x_plus_five, five));

    // x + 5 < 5 |= -x >= 0 --> true
    TS_ASSERT(ArithEntail::checkWithAssumption(
        x_plus_five_lt_five, neg_x, zero, false));

    // x + 5 < 5 |= 0 > x --> true
    TS_ASSERT(
        ArithEntail::checkWithAssumption(x_plus_five_lt_five, zero, x, false));

    // 0 < x |= x >= (str.len (int.to.str x))
    Node assm = Rewriter::rewrite(d_nm->mkNode(kind::LT, zero, x));
    TS_ASSERT(ArithEntail::checkWithAssumption(
        assm,
        x,
        d_nm->mkNode(kind::STRING_LENGTH, d_nm->mkNode(kind::STRING_ITOS, x)),
        false));
  }

  void testRewriteSubstr()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node negone = d_nm->mkConst(Rational(-1));
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));

    Node s = d_nm->mkVar("s", strType);
    Node s2 = d_nm->mkVar("s2", strType);
    Node x = d_nm->mkVar("x", intType);
    Node y = d_nm->mkVar("y", intType);

    // (str.substr "A" x x) --> ""
    Node n = d_nm->mkNode(kind::STRING_SUBSTR, a, x, x);
    Node res = StringsRewriter(nullptr).rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "A" (+ x 1) x) -> ""
    n = d_nm->mkNode(kind::STRING_SUBSTR,
                     a,
                     d_nm->mkNode(kind::PLUS, x, d_nm->mkConst(Rational(1))),
                     x);
    res = StringsRewriter(nullptr).rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "A" (+ x (str.len s2)) x) -> ""
    n = d_nm->mkNode(
        kind::STRING_SUBSTR,
        a,
        d_nm->mkNode(kind::PLUS, x, d_nm->mkNode(kind::STRING_LENGTH, s)),
        x);
    res = StringsRewriter(nullptr).rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "A" x y) -> (str.substr "A" x y)
    n = d_nm->mkNode(kind::STRING_SUBSTR, a, x, y);
    res = StringsRewriter(nullptr).rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, n);

    // (str.substr "ABCD" (+ x 3) x) -> ""
    n = d_nm->mkNode(
        kind::STRING_SUBSTR, abcd, d_nm->mkNode(kind::PLUS, x, three), x);
    res = StringsRewriter(nullptr).rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "ABCD" (+ x 2) x) -> (str.substr "ABCD" (+ x 2) x)
    n = d_nm->mkNode(
        kind::STRING_SUBSTR, abcd, d_nm->mkNode(kind::PLUS, x, two), x);
    res = StringsRewriter(nullptr).rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, n);

    // (str.substr (str.substr s x x) x x) -> ""
    n = d_nm->mkNode(
        kind::STRING_SUBSTR, d_nm->mkNode(kind::STRING_SUBSTR, s, x, x), x, x);
    sameNormalForm(n, empty);

    // Same normal form for:
    //
    // (str.substr (str.replace "" s "B") x x)
    //
    // (str.replace "" s (str.substr "B" x x)))
    Node lhs = d_nm->mkNode(kind::STRING_SUBSTR,
                            d_nm->mkNode(kind::STRING_STRREPL, empty, s, b),
                            x,
                            x);
    Node rhs = d_nm->mkNode(kind::STRING_STRREPL,
                            empty,
                            s,
                            d_nm->mkNode(kind::STRING_SUBSTR, b, x, x));
    sameNormalForm(lhs, rhs);

    // Same normal form:
    //
    // (str.substr (str.replace s "A" "B") 0 x)
    //
    // (str.replace (str.substr s 0 x) "A" "B")
    Node substr_repl = d_nm->mkNode(kind::STRING_SUBSTR,
                                    d_nm->mkNode(kind::STRING_STRREPL, s, a, b),
                                    zero,
                                    x);
    Node repl_substr =
        d_nm->mkNode(kind::STRING_STRREPL,
                     d_nm->mkNode(kind::STRING_SUBSTR, s, zero, x),
                     a,
                     b);
    sameNormalForm(substr_repl, repl_substr);

    // Same normal form:
    //
    // (str.substr (str.replace s (str.substr (str.++ s2 "A") 0 1) "B") 0 x)
    //
    // (str.replace (str.substr s 0 x) (str.substr (str.++ s2 "A") 0 1) "B")
    Node substr_y = d_nm->mkNode(kind::STRING_SUBSTR,
                                 d_nm->mkNode(kind::STRING_CONCAT, s2, a),
                                 zero,
                                 one);
    substr_repl =
        d_nm->mkNode(kind::STRING_SUBSTR,
                     d_nm->mkNode(kind::STRING_STRREPL, s, substr_y, b),
                     zero,
                     x);
    repl_substr = d_nm->mkNode(kind::STRING_STRREPL,
                               d_nm->mkNode(kind::STRING_SUBSTR, s, zero, x),
                               substr_y,
                               b);
    sameNormalForm(substr_repl, repl_substr);

    // (str.substr (str.int.to.str x) x x) ---> empty
    Node substr_itos = d_nm->mkNode(
        kind::STRING_SUBSTR, d_nm->mkNode(kind::STRING_ITOS, x), x, x);
    sameNormalForm(substr_itos, empty);

    // (str.substr s (* (- 1) (str.len s)) 1) ---> empty
    Node substr = d_nm->mkNode(
        kind::STRING_SUBSTR,
        s,
        d_nm->mkNode(kind::MULT, negone, d_nm->mkNode(kind::STRING_LENGTH, s)),
        one);
    sameNormalForm(substr, empty);
  }

  void testRewriteConcat()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node zero = d_nm->mkConst(Rational(0));
    Node three = d_nm->mkConst(Rational(3));

    Node i = d_nm->mkVar("i", intType);
    Node s = d_nm->mkVar("s", strType);
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);

    // Same normal form for:
    //
    // (str.++ (str.replace "A" x "") "A")
    //
    // (str.++ "A" (str.replace "A" x ""))
    Node repl_a_x_e = d_nm->mkNode(kind::STRING_STRREPL, a, x, empty);
    Node repl_a = d_nm->mkNode(kind::STRING_CONCAT, repl_a_x_e, a);
    Node a_repl = d_nm->mkNode(kind::STRING_CONCAT, a, repl_a_x_e);
    sameNormalForm(repl_a, a_repl);

    // Same normal form for:
    //
    // (str.++ y (str.replace "" x (str.substr y 0 3)) (str.substr y 0 3) "A" (str.substr y 0 3))
    //
    // (str.++ y (str.substr y 0 3) (str.replace "" x (str.substr y 0 3)) "A" (str.substr y 0 3))
    Node z = d_nm->mkNode(kind::STRING_SUBSTR, y, zero, three);
    Node repl_e_x_z = d_nm->mkNode(kind::STRING_STRREPL, empty, x, z);
    repl_a = d_nm->mkNode(kind::STRING_CONCAT, y, repl_e_x_z, z, a, z);
    a_repl = d_nm->mkNode(kind::STRING_CONCAT, y, z, repl_e_x_z, a, z);
    sameNormalForm(repl_a, a_repl);

    // Same normal form for:
    //
    // (str.++ "A" (str.replace "A" x "") (str.substr "A" 0 i))
    //
    // (str.++ (str.substr "A" 0 i) (str.replace "A" x "") "A")
    Node substr_a = d_nm->mkNode(kind::STRING_SUBSTR, a, zero, i);
    Node a_substr_repl =
        d_nm->mkNode(kind::STRING_CONCAT, a, substr_a, repl_a_x_e);
    Node substr_repl_a =
        d_nm->mkNode(kind::STRING_CONCAT, substr_a, repl_a_x_e, a);
    sameNormalForm(a_substr_repl, substr_repl_a);

    // Same normal form for:
    //
    // (str.++ (str.replace "" x (str.substr "A" 0 i)) (str.substr "A" 0 i) (str.at "A" i))
    //
    // (str.++ (str.at "A" i) (str.replace "" x (str.substr "A" 0 i)) (str.substr "A" 0 i))
    Node charat_a = d_nm->mkNode(kind::STRING_CHARAT, a, i);
    Node repl_e_x_s = d_nm->mkNode(kind::STRING_STRREPL, empty, x, substr_a);
    Node repl_substr_a =
        d_nm->mkNode(kind::STRING_CONCAT, repl_e_x_s, substr_a, charat_a);
    Node a_repl_substr =
        d_nm->mkNode(kind::STRING_CONCAT, charat_a, repl_e_x_s, substr_a);
    sameNormalForm(repl_substr_a, a_repl_substr);
  }

  void testLengthPreserveRewrite()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node f = d_nm->mkConst(::CVC4::String("F"));
    Node gh = d_nm->mkConst(::CVC4::String("GH"));
    Node ij = d_nm->mkConst(::CVC4::String("IJ"));

    Node i = d_nm->mkVar("i", intType);
    Node s = d_nm->mkVar("s", strType);
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);

    // Same length preserving rewrite for:
    //
    // (str.++ "ABCD" (str.++ x x))
    //
    // (str.++ "GH" (str.repl "GH" "IJ") "IJ")
    Node concat1 = d_nm->mkNode(
        kind::STRING_CONCAT, abcd, d_nm->mkNode(kind::STRING_CONCAT, x, x));
    Node concat2 = d_nm->mkNode(kind::STRING_CONCAT,
                                gh,
                                x,
                                d_nm->mkNode(kind::STRING_STRREPL, x, gh, ij),
                                ij);
    Node res_concat1 = SequencesRewriter::lengthPreserveRewrite(concat1);
    Node res_concat2 = SequencesRewriter::lengthPreserveRewrite(concat2);
    TS_ASSERT_EQUALS(res_concat1, res_concat2);
  }

  void testRewriteIndexOf()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node aaad = d_nm->mkConst(::CVC4::String("AAAD"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node c = d_nm->mkConst(::CVC4::String("C"));
    Node ccc = d_nm->mkConst(::CVC4::String("CCC"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node negOne = d_nm->mkConst(Rational(-1));
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));
    Node i = d_nm->mkVar("i", intType);
    Node j = d_nm->mkVar("j", intType);

    // Same normal form for:
    //
    // (str.to.int (str.indexof "A" x 1))
    //
    // (str.to.int (str.indexof "B" x 1))
    Node a_idof_x = d_nm->mkNode(kind::STRING_STRIDOF, a, x, two);
    Node itos_a_idof_x = d_nm->mkNode(kind::STRING_ITOS, a_idof_x);
    Node b_idof_x = d_nm->mkNode(kind::STRING_STRIDOF, b, x, two);
    Node itos_b_idof_x = d_nm->mkNode(kind::STRING_ITOS, b_idof_x);
    sameNormalForm(itos_a_idof_x, itos_b_idof_x);

    // Same normal form for:
    //
    // (str.indexof (str.++ "ABCD" x) y 3)
    //
    // (str.indexof (str.++ "AAAD" x) y 3)
    Node idof_abcd = d_nm->mkNode(kind::STRING_STRIDOF,
                                  d_nm->mkNode(kind::STRING_CONCAT, abcd, x),
                                  y,
                                  three);
    Node idof_aaad = d_nm->mkNode(kind::STRING_STRIDOF,
                                  d_nm->mkNode(kind::STRING_CONCAT, aaad, x),
                                  y,
                                  three);
    sameNormalForm(idof_abcd, idof_aaad);

    // (str.indexof (str.substr x 1 i) "A" i) ---> -1
    Node idof_substr =
        d_nm->mkNode(kind::STRING_STRIDOF,
                     d_nm->mkNode(kind::STRING_SUBSTR, x, one, i),
                     a,
                     i);
    sameNormalForm(idof_substr, negOne);

    {
      // Same normal form for:
      //
      // (str.indexof (str.++ "B" (str.substr "CCC" i j) x "A") "A" 0)
      //
      // (+ 1 (str.len (str.substr "CCC" i j))
      //    (str.indexof (str.++ "A" x y) "A" 0))
      Node lhs = d_nm->mkNode(
          kind::STRING_STRIDOF,
          d_nm->mkNode(kind::STRING_CONCAT,
                       b,
                       d_nm->mkNode(kind::STRING_SUBSTR, ccc, i, j),
                       x,
                       a),
          a,
          zero);
      Node rhs = d_nm->mkNode(
          kind::PLUS,
          one,
          d_nm->mkNode(kind::STRING_LENGTH,
                       d_nm->mkNode(kind::STRING_SUBSTR, ccc, i, j)),
          d_nm->mkNode(kind::STRING_STRIDOF,
                       d_nm->mkNode(kind::STRING_CONCAT, x, a),
                       a,
                       zero));
      sameNormalForm(lhs, rhs);
    }

    {
      // Same normal form for:
      //
      // (str.indexof (str.++ "B" "C" "A" x y) "A" 0)
      //
      // (+ 2 (str.indexof (str.++ "A" x y) "A" 0))
      Node lhs = d_nm->mkNode(kind::STRING_STRIDOF,
                              d_nm->mkNode(kind::STRING_CONCAT, b, c, a, x, y),
                              a,
                              zero);
      Node rhs =
          d_nm->mkNode(kind::PLUS,
                       two,
                       d_nm->mkNode(kind::STRING_STRIDOF,
                                    d_nm->mkNode(kind::STRING_CONCAT, a, x, y),
                                    a,
                                    zero));
      sameNormalForm(lhs, rhs);
    }
  }

  void testRewriteReplace()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node ab = d_nm->mkConst(::CVC4::String("AB"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node c = d_nm->mkConst(::CVC4::String("C"));
    Node d = d_nm->mkConst(::CVC4::String("D"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", strType);
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node n = d_nm->mkVar("n", intType);

    // (str.replace (str.replace x "B" x) x "A") -->
    //   (str.replace (str.replace x "B" "A") x "A")
    Node repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                                  d_nm->mkNode(kind::STRING_STRREPL, x, b, x),
                                  x,
                                  a);
    Node repl_repl_short =
        d_nm->mkNode(kind::STRING_STRREPL,
                     d_nm->mkNode(kind::STRING_STRREPL, x, b, a),
                     x,
                     a);
    sameNormalForm(repl_repl, repl_repl_short);

    // (str.replace "A" (str.replace "B", x, "C") "D") --> "A"
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             a,
                             d_nm->mkNode(kind::STRING_STRREPL, b, x, c),
                             d);
    sameNormalForm(repl_repl, a);

    // (str.replace "A" (str.replace "B", x, "A") "D") -/-> "A"
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             a,
                             d_nm->mkNode(kind::STRING_STRREPL, b, x, a),
                             d);
    differentNormalForms(repl_repl, a);

    // Same normal form for:
    //
    // (str.replace x (str.++ x y z) y)
    //
    // (str.replace x (str.++ x y z) z)
    Node xyz = d_nm->mkNode(kind::STRING_CONCAT, x, y, z);
    Node repl_x_xyz = d_nm->mkNode(kind::STRING_STRREPL, x, xyz, y);
    Node repl_x_zyx = d_nm->mkNode(kind::STRING_STRREPL, x, xyz, z);
    sameNormalForm(repl_x_xyz, repl_x_zyx);

    // (str.replace "" (str.++ x x) x) --> ""
    Node repl_empty_xx = d_nm->mkNode(kind::STRING_STRREPL,
                                      empty,
                                      d_nm->mkNode(kind::STRING_CONCAT, x, x),
                                      x);
    sameNormalForm(repl_empty_xx, empty);

    // (str.replace "AB" (str.++ x "A") x) --> (str.replace "AB" (str.++ x "A")
    // "")
    Node repl_ab_xa_x = d_nm->mkNode(kind::STRING_STRREPL,
                                     d_nm->mkNode(kind::STRING_CONCAT, a, b),
                                     d_nm->mkNode(kind::STRING_CONCAT, x, a),
                                     x);
    Node repl_ab_xa_e = d_nm->mkNode(kind::STRING_STRREPL,
                                     d_nm->mkNode(kind::STRING_CONCAT, a, b),
                                     d_nm->mkNode(kind::STRING_CONCAT, x, a),
                                     empty);
    sameNormalForm(repl_ab_xa_x, repl_ab_xa_e);

    // (str.replace "AB" (str.++ x "A") x) -/-> (str.replace "AB" (str.++ "A" x)
    // "")
    Node repl_ab_ax_e = d_nm->mkNode(kind::STRING_STRREPL,
                                     d_nm->mkNode(kind::STRING_CONCAT, a, b),
                                     d_nm->mkNode(kind::STRING_CONCAT, a, x),
                                     empty);
    differentNormalForms(repl_ab_ax_e, repl_ab_xa_e);

    // (str.replace "" (str.replace y x "A") y) ---> ""
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             empty,
                             d_nm->mkNode(kind::STRING_STRREPL, y, x, a),
                             y);
    sameNormalForm(repl_repl, empty);

    // (str.replace "" (str.replace x y x) x) ---> ""
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             empty,
                             d_nm->mkNode(kind::STRING_STRREPL, x, y, x),
                             x);
    sameNormalForm(repl_repl, empty);

    // (str.replace "" (str.substr x 0 1) x) ---> ""
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             empty,
                             d_nm->mkNode(kind::STRING_SUBSTR, x, zero, one),
                             x);
    sameNormalForm(repl_repl, empty);

    // Same normal form for:
    //
    // (str.replace "" (str.replace x y x) y)
    //
    // (str.replace "" x y)
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             empty,
                             d_nm->mkNode(kind::STRING_STRREPL, x, y, x),
                             y);
    Node repl = d_nm->mkNode(kind::STRING_STRREPL, empty, x, y);
    sameNormalForm(repl_repl, repl);

    // Same normal form:
    //
    // (str.replace "B" (str.replace x "A" "B") "B")
    //
    // (str.replace "B" x "B"))
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             b,
                             d_nm->mkNode(kind::STRING_STRREPL, x, a, b),
                             b);
    repl = d_nm->mkNode(kind::STRING_STRREPL, b, x, b);
    sameNormalForm(repl_repl, repl);

    // Different normal forms for:
    //
    // (str.replace "B" (str.replace "" x "A") "B")
    //
    // (str.replace "B" x "B")
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             b,
                             d_nm->mkNode(kind::STRING_STRREPL, empty, x, a),
                             b);
    repl = d_nm->mkNode(kind::STRING_STRREPL, b, x, b);
    differentNormalForms(repl_repl, repl);

    {
      // Same normal form:
      //
      // (str.replace (str.++ "AB" x) "C" y)
      //
      // (str.++ "AB" (str.replace x "C" y))
      Node lhs = d_nm->mkNode(
          kind::STRING_STRREPL, d_nm->mkNode(kind::STRING_CONCAT, ab, x), c, y);
      Node rhs = d_nm->mkNode(
          kind::STRING_CONCAT, ab, d_nm->mkNode(kind::STRING_STRREPL, x, c, y));
      sameNormalForm(lhs, rhs);
    }
  }

  void testRewriteReplaceRe()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    std::vector<Node> emptyVec;
    Node sigStar = d_nm->mkNode(kind::REGEXP_STAR,
                                d_nm->mkNode(kind::REGEXP_SIGMA, emptyVec));
    Node foo = d_nm->mkConst(String("FOO"));
    Node a = d_nm->mkConst(String("A"));
    Node b = d_nm->mkConst(String("B"));
    Node re = d_nm->mkNode(kind::REGEXP_CONCAT,
                           d_nm->mkNode(kind::STRING_TO_REGEXP, a),
                           sigStar,
                           d_nm->mkNode(kind::STRING_TO_REGEXP, b));

    // Same normal form:
    //
    // (str.replace_re
    //   "AZZZB"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "FOO"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE, d_nm->mkConst(String("AZZZB")), re, foo);
      Node res = d_nm->mkConst(::CVC4::String("FOO"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZAZZZBZZB"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "ZFOOZZB"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE, d_nm->mkConst(String("ZAZZZBZZB")), re, foo);
      Node res = d_nm->mkConst(::CVC4::String("ZFOOZZB"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZAZZZBZAZB"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "ZFOOZAZB"
    {
      Node t = d_nm->mkNode(kind::STRING_REPLACE_RE,
                            d_nm->mkConst(String("ZAZZZBZAZB")),
                            re,
                            foo);
      Node res = d_nm->mkConst(::CVC4::String("ZFOOZAZB"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZZZ"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "ZZZ"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE, d_nm->mkConst(String("ZZZ")), re, foo);
      Node res = d_nm->mkConst(::CVC4::String("ZZZ"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZZZ"
    //   re.all
    //   "FOO")
    //
    // "FOOZZZ"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE, d_nm->mkConst(String("ZZZ")), sigStar, foo);
      Node res = d_nm->mkConst(::CVC4::String("FOOZZZ"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   ""
    //   re.all
    //   "FOO")
    //
    // "FOO"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE, d_nm->mkConst(String("")), sigStar, foo);
      Node res = d_nm->mkConst(::CVC4::String("FOO"));
      sameNormalForm(t, res);
    }
  }

  void testRewriteReplaceReAll()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    std::vector<Node> emptyVec;
    Node sigStar = d_nm->mkNode(kind::REGEXP_STAR,
                                d_nm->mkNode(kind::REGEXP_SIGMA, emptyVec));
    Node foo = d_nm->mkConst(String("FOO"));
    Node a = d_nm->mkConst(String("A"));
    Node b = d_nm->mkConst(String("B"));
    Node re = d_nm->mkNode(kind::REGEXP_CONCAT,
                           d_nm->mkNode(kind::STRING_TO_REGEXP, a),
                           sigStar,
                           d_nm->mkNode(kind::STRING_TO_REGEXP, b));

    // Same normal form:
    //
    // (str.replace_re
    //   "AZZZB"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "FOO"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE_ALL, d_nm->mkConst(String("AZZZB")), re, foo);
      Node res = d_nm->mkConst(::CVC4::String("FOO"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZAZZZBZZB"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "ZFOOZZB"
    {
      Node t = d_nm->mkNode(kind::STRING_REPLACE_RE_ALL,
                            d_nm->mkConst(String("ZAZZZBZZB")),
                            re,
                            foo);
      Node res = d_nm->mkConst(::CVC4::String("ZFOOZZB"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZAZZZBZAZB"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "ZFOOZFOO"
    {
      Node t = d_nm->mkNode(kind::STRING_REPLACE_RE_ALL,
                            d_nm->mkConst(String("ZAZZZBZAZB")),
                            re,
                            foo);
      Node res = d_nm->mkConst(::CVC4::String("ZFOOZFOO"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZZZ"
    //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
    //   "FOO")
    //
    // "ZZZ"
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE_ALL, d_nm->mkConst(String("ZZZ")), re, foo);
      Node res = d_nm->mkConst(::CVC4::String("ZZZ"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   "ZZZ"
    //   re.all
    //   "FOO")
    //
    // "FOOFOOFOO"
    {
      Node t = d_nm->mkNode(kind::STRING_REPLACE_RE_ALL,
                            d_nm->mkConst(String("ZZZ")),
                            sigStar,
                            foo);
      Node res = d_nm->mkConst(::CVC4::String("FOOFOOFOO"));
      sameNormalForm(t, res);
    }

    // Same normal form:
    //
    // (str.replace_re
    //   ""
    //   re.all
    //   "FOO")
    //
    // ""
    {
      Node t = d_nm->mkNode(
          kind::STRING_REPLACE_RE_ALL, d_nm->mkConst(String("")), sigStar, foo);
      Node res = d_nm->mkConst(::CVC4::String(""));
      sameNormalForm(t, res);
    }
  }

  void testRewriteContains()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node ab = d_nm->mkConst(::CVC4::String("AB"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node c = d_nm->mkConst(::CVC4::String("C"));
    Node e = d_nm->mkConst(::CVC4::String("E"));
    Node h = d_nm->mkConst(::CVC4::String("H"));
    Node j = d_nm->mkConst(::CVC4::String("J"));
    Node p = d_nm->mkConst(::CVC4::String("P"));
    Node abc = d_nm->mkConst(::CVC4::String("ABC"));
    Node def = d_nm->mkConst(::CVC4::String("DEF"));
    Node ghi = d_nm->mkConst(::CVC4::String("GHI"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node xy = d_nm->mkNode(kind::STRING_CONCAT, x, y);
    Node yx = d_nm->mkNode(kind::STRING_CONCAT, y, x);
    Node z = d_nm->mkVar("z", strType);
    Node n = d_nm->mkVar("n", intType);
    Node m = d_nm->mkVar("m", intType);
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));
    Node four = d_nm->mkConst(Rational(4));
    Node t = d_nm->mkConst(true);
    Node f = d_nm->mkConst(false);

    // Same normal form for:
    //
    // (str.replace "A" (str.substr x 1 3) y z)
    //
    // (str.replace "A" (str.substr x 1 4) y z)
    Node substr_3 =
        d_nm->mkNode(kind::STRING_STRREPL,
                     a,
                     d_nm->mkNode(kind::STRING_SUBSTR, x, one, three),
                     z);
    Node substr_4 =
        d_nm->mkNode(kind::STRING_STRREPL,
                     a,
                     d_nm->mkNode(kind::STRING_SUBSTR, x, one, four),
                     z);
    sameNormalForm(substr_3, substr_4);

    // Same normal form for:
    //
    // (str.replace "A" (str.++ y (str.substr x 1 3)) y z)
    //
    // (str.replace "A" (str.++ y (str.substr x 1 4)) y z)
    Node concat_substr_3 = d_nm->mkNode(
        kind::STRING_STRREPL,
        a,
        d_nm->mkNode(kind::STRING_CONCAT,
                     y,
                     d_nm->mkNode(kind::STRING_SUBSTR, x, one, three)),
        z);
    Node concat_substr_4 = d_nm->mkNode(
        kind::STRING_STRREPL,
        a,
        d_nm->mkNode(kind::STRING_CONCAT,
                     y,
                     d_nm->mkNode(kind::STRING_SUBSTR, x, one, four)),
        z);
    sameNormalForm(concat_substr_3, concat_substr_4);

    // (str.contains "A" (str.++ a (str.replace "B", x, "C")) --> false
    Node ctn_repl =
        d_nm->mkNode(kind::STRING_STRCTN,
                     a,
                     d_nm->mkNode(kind::STRING_CONCAT,
                                  a,
                                  d_nm->mkNode(kind::STRING_STRREPL, b, x, c)));
    sameNormalForm(ctn_repl, f);

    // (str.contains x (str.++ x x)) --> (= x "")
    Node x_cnts_x_x = d_nm->mkNode(
        kind::STRING_STRCTN, x, d_nm->mkNode(kind::STRING_CONCAT, x, x));
    sameNormalForm(x_cnts_x_x, d_nm->mkNode(kind::EQUAL, x, empty));

    // Same normal form for:
    //
    // (str.contains (str.++ y x) (str.++ x z y))
    //
    // (and (str.contains (str.++ y x) (str.++ x y)) (= z ""))
    Node yx_cnts_xzy = d_nm->mkNode(
        kind::STRING_STRCTN, yx, d_nm->mkNode(kind::STRING_CONCAT, x, z, y));
    Node yx_cnts_xy = d_nm->mkNode(kind::AND,
                                   d_nm->mkNode(kind::EQUAL, z, empty),
                                   d_nm->mkNode(kind::STRING_STRCTN, yx, xy));
    sameNormalForm(yx_cnts_xzy, yx_cnts_xy);

    // Same normal form for:
    //
    // (str.contains (str.substr x n (str.len y)) y)
    //
    // (= (str.substr x n (str.len y)) y)
    Node ctn_substr = d_nm->mkNode(
        kind::STRING_STRCTN,
        d_nm->mkNode(
            kind::STRING_SUBSTR, x, n, d_nm->mkNode(kind::STRING_LENGTH, y)),
        y);
    Node substr_eq = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::STRING_SUBSTR, x, n, d_nm->mkNode(kind::STRING_LENGTH, y)),
        y);
    sameNormalForm(ctn_substr, substr_eq);

    // Same normal form for:
    //
    // (str.contains x (str.replace y x y))
    //
    // (str.contains x y)
    Node ctn_repl_y_x_y = d_nm->mkNode(
        kind::STRING_STRCTN, x, d_nm->mkNode(kind::STRING_STRREPL, y, x, y));
    Node ctn_x_y = d_nm->mkNode(kind::STRING_STRCTN, x, y);
    sameNormalForm(ctn_repl_y_x_y, ctn_repl_y_x_y);

    // Same normal form for:
    //
    // (str.contains x (str.replace x y x))
    //
    // (= x (str.replace x y x))
    Node ctn_repl_self = d_nm->mkNode(
        kind::STRING_STRCTN, x, d_nm->mkNode(kind::STRING_STRREPL, x, y, x));
    Node eq_repl = d_nm->mkNode(
        kind::EQUAL, x, d_nm->mkNode(kind::STRING_STRREPL, x, y, x));
    sameNormalForm(ctn_repl_self, eq_repl);

    // (str.contains x (str.++ "A" (str.replace x y x))) ---> false
    Node ctn_repl_self_f =
        d_nm->mkNode(kind::STRING_STRCTN,
                     x,
                     d_nm->mkNode(kind::STRING_CONCAT,
                                  a,
                                  d_nm->mkNode(kind::STRING_STRREPL, x, y, x)));
    sameNormalForm(ctn_repl_self_f, f);

    // Same normal form for:
    //
    // (str.contains x (str.replace "" x y))
    //
    // (= "" (str.replace "" x y))
    Node ctn_repl_empty =
        d_nm->mkNode(kind::STRING_STRCTN,
                     x,
                     d_nm->mkNode(kind::STRING_STRREPL, empty, x, y));
    Node eq_repl_empty = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_STRREPL, empty, x, y));
    sameNormalForm(ctn_repl_empty, eq_repl_empty);

    // Same normal form for:
    //
    // (str.contains x (str.++ x y))
    //
    // (= "" y)
    Node ctn_x_x_y = d_nm->mkNode(
        kind::STRING_STRCTN, x, d_nm->mkNode(kind::STRING_CONCAT, x, y));
    Node eq_emp_y = d_nm->mkNode(kind::EQUAL, empty, y);
    sameNormalForm(ctn_x_x_y, eq_emp_y);

    // Same normal form for:
    //
    // (str.contains (str.++ y x) (str.++ x y))
    //
    // (= (str.++ y x) (str.++ x y))
    Node ctn_yxxy = d_nm->mkNode(kind::STRING_STRCTN, yx, xy);
    Node eq_yxxy = d_nm->mkNode(kind::EQUAL, yx, xy);
    sameNormalForm(ctn_yxxy, eq_yxxy);

    // (str.contains (str.replace x y x) x) ---> true
    ctn_repl = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, x, y, x), x);
    sameNormalForm(ctn_repl, t);

    // (str.contains (str.replace (str.++ x y) z (str.++ y x)) x) ---> true
    ctn_repl = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, xy, z, yx), x);
    sameNormalForm(ctn_repl, t);

    // (str.contains (str.++ z (str.replace (str.++ x y) z (str.++ y x))) x)
    //   ---> true
    ctn_repl = d_nm->mkNode(
        kind::STRING_STRCTN,
        d_nm->mkNode(kind::STRING_CONCAT,
                     z,
                     d_nm->mkNode(kind::STRING_STRREPL, xy, z, yx)),
        x);
    sameNormalForm(ctn_repl, t);

    // Same normal form for:
    //
    // (str.contains (str.replace x y x) y)
    //
    // (str.contains x y)
    Node lhs = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, x, y, x), y);
    Node rhs = d_nm->mkNode(kind::STRING_STRCTN, x, y);
    sameNormalForm(lhs, rhs);

    // Same normal form for:
    //
    // (str.contains (str.replace x y x) "B")
    //
    // (str.contains x "B")
    lhs = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, x, y, x), b);
    rhs = d_nm->mkNode(kind::STRING_STRCTN, x, b);
    sameNormalForm(lhs, rhs);

    // Same normal form for:
    //
    // (str.contains (str.replace x y x) (str.substr z n 1))
    //
    // (str.contains x (str.substr z n 1))
    Node substr_z = d_nm->mkNode(kind::STRING_SUBSTR, z, n, one);
    lhs = d_nm->mkNode(kind::STRING_STRCTN,
                       d_nm->mkNode(kind::STRING_STRREPL, x, y, x),
                       substr_z);
    rhs = d_nm->mkNode(kind::STRING_STRCTN, x, substr_z);
    sameNormalForm(lhs, rhs);

    // Same normal form for:
    //
    // (str.contains (str.replace x y z) z)
    //
    // (str.contains (str.replace x z y) y)
    lhs = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, x, y, z), z);
    rhs = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, x, z, y), y);
    sameNormalForm(lhs, rhs);

    // Same normal form for:
    //
    // (str.contains (str.replace x "A" "B") "A")
    //
    // (str.contains (str.replace x "A" "") "A")
    lhs = d_nm->mkNode(
        kind::STRING_STRCTN, d_nm->mkNode(kind::STRING_STRREPL, x, a, b), a);
    rhs = d_nm->mkNode(kind::STRING_STRCTN,
                       d_nm->mkNode(kind::STRING_STRREPL, x, a, empty),
                       a);
    sameNormalForm(lhs, rhs);

    {
      // (str.contains (str.++ x "A") (str.++ "B" x)) ---> false
      Node ctn = d_nm->mkNode(kind::STRING_STRCTN,
                              d_nm->mkNode(kind::STRING_CONCAT, x, a),
                              d_nm->mkNode(kind::STRING_CONCAT, b, x));
      sameNormalForm(ctn, f);
    }

    {
      // Same normal form for:
      //
      // (str.contains (str.replace x "ABC" "DEF") "GHI")
      //
      // (str.contains x "GHI")
      lhs = d_nm->mkNode(kind::STRING_STRCTN,
                         d_nm->mkNode(kind::STRING_STRREPL, x, abc, def),
                         ghi);
      rhs = d_nm->mkNode(kind::STRING_STRCTN, x, ghi);
      sameNormalForm(lhs, rhs);
    }

    {
      // Different normal forms for:
      //
      // (str.contains (str.replace x "ABC" "DEF") "B")
      //
      // (str.contains x "B")
      lhs = d_nm->mkNode(kind::STRING_STRCTN,
                         d_nm->mkNode(kind::STRING_STRREPL, x, abc, def),
                         b);
      rhs = d_nm->mkNode(kind::STRING_STRCTN, x, b);
      differentNormalForms(lhs, rhs);
    }

    {
      // Different normal forms for:
      //
      // (str.contains (str.replace x "B" "DEF") "ABC")
      //
      // (str.contains x "ABC")
      lhs = d_nm->mkNode(kind::STRING_STRCTN,
                         d_nm->mkNode(kind::STRING_STRREPL, x, b, def),
                         abc);
      rhs = d_nm->mkNode(kind::STRING_STRCTN, x, abc);
      differentNormalForms(lhs, rhs);
    }

    {
      // Same normal form for:
      //
      // (str.contains (str.++ (str.substr "DEF" n m) x) "AB")
      //
      // (str.contains x "AB")
      lhs = d_nm->mkNode(
          kind::STRING_STRCTN,
          d_nm->mkNode(kind::STRING_CONCAT,
                       d_nm->mkNode(kind::STRING_SUBSTR, def, n, m),
                       x),
          ab);
      rhs = d_nm->mkNode(kind::STRING_STRCTN, x, ab);
      sameNormalForm(lhs, rhs);
    }

    {
      // Same normal form for:
      //
      // (str.contains "ABC" (str.at x n))
      //
      // (or (= x "")
      //     (= x "A") (= x "B") (= x "C"))
      Node cat = d_nm->mkNode(kind::STRING_CHARAT, x, n);
      lhs = d_nm->mkNode(kind::STRING_STRCTN, abc, cat);
      rhs = d_nm->mkNode(kind::OR,
                         d_nm->mkNode(kind::EQUAL, cat, empty),
                         d_nm->mkNode(kind::EQUAL, cat, a),
                         d_nm->mkNode(kind::EQUAL, cat, b),
                         d_nm->mkNode(kind::EQUAL, cat, c));
      sameNormalForm(lhs, rhs);
    }
  }

  void testInferEqsFromContains()
  {
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node xy = d_nm->mkNode(kind::STRING_CONCAT, x, y);
    Node f = d_nm->mkConst(false);

    // inferEqsFromContains("", (str.++ x y)) returns something equivalent to
    // (= "" y)
    Node empty_x_y = d_nm->mkNode(kind::AND,
                                  d_nm->mkNode(kind::EQUAL, empty, x),
                                  d_nm->mkNode(kind::EQUAL, empty, y));
    sameNormalForm(StringsEntail::inferEqsFromContains(empty, xy), empty_x_y);

    // inferEqsFromContains(x, (str.++ x y)) returns false
    Node bxya = d_nm->mkNode(kind::STRING_CONCAT, b, y, x, a);
    sameNormalForm(StringsEntail::inferEqsFromContains(x, bxya), f);

    // inferEqsFromContains(x, y) returns null
    Node n = StringsEntail::inferEqsFromContains(x, y);
    TS_ASSERT(n.isNull());

    // inferEqsFromContains(x, x) returns something equivalent to (= x x)
    Node eq_x_x = d_nm->mkNode(kind::EQUAL, x, x);
    sameNormalForm(StringsEntail::inferEqsFromContains(x, x), eq_x_x);

    // inferEqsFromContains((str.replace x "B" "A"), x) returns something
    // equivalent to (= (str.replace x "B" "A") x)
    Node repl = d_nm->mkNode(kind::STRING_STRREPL, x, b, a);
    Node eq_repl_x = d_nm->mkNode(kind::EQUAL, repl, x);
    sameNormalForm(StringsEntail::inferEqsFromContains(repl, x), eq_repl_x);

    // inferEqsFromContains(x, (str.replace x "B" "A")) returns something
    // equivalent to (= (str.replace x "B" "A") x)
    Node eq_x_repl = d_nm->mkNode(kind::EQUAL, x, repl);
    sameNormalForm(StringsEntail::inferEqsFromContains(x, repl), eq_x_repl);
  }

  void testRewritePrefixSuffix()
  {
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node xx = d_nm->mkNode(kind::STRING_CONCAT, x, x);
    Node xxa = d_nm->mkNode(kind::STRING_CONCAT, x, x, a);
    Node xy = d_nm->mkNode(kind::STRING_CONCAT, x, y);
    Node f = d_nm->mkConst(false);

    // Same normal form for:
    //
    // (str.prefix (str.++ x y) x)
    //
    // (= y "")
    Node p_xy = d_nm->mkNode(kind::STRING_PREFIX, xy, x);
    Node empty_y = d_nm->mkNode(kind::EQUAL, y, empty);
    sameNormalForm(p_xy, empty_y);

    // Same normal form for:
    //
    // (str.suffix (str.++ x x) x)
    //
    // (= x "")
    Node p_xx = d_nm->mkNode(kind::STRING_SUFFIX, xx, x);
    Node empty_x = d_nm->mkNode(kind::EQUAL, x, empty);
    sameNormalForm(p_xx, empty_x);

    // (str.suffix x (str.++ x x "A")) ---> false
    Node p_xxa = d_nm->mkNode(kind::STRING_SUFFIX, xxa, x);
    sameNormalForm(p_xxa, f);
  }

  void testRewriteEqualityExt()
  {
    TypeNode strType = d_nm->stringType();
    TypeNode intType = d_nm->integerType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node aaa = d_nm->mkConst(::CVC4::String("AAA"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node ba = d_nm->mkConst(::CVC4::String("BA"));
    Node w = d_nm->mkVar("w", strType);
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", strType);
    Node xxa = d_nm->mkNode(kind::STRING_CONCAT, x, x, a);
    Node f = d_nm->mkConst(false);
    Node n = d_nm->mkVar("n", intType);
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node three = d_nm->mkConst(Rational(3));

    // Same normal form for:
    //
    // (= "" (str.replace "" x "B"))
    //
    // (not (= x ""))
    Node empty_repl = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_STRREPL, empty, x, b));
    Node empty_x = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, empty));
    sameNormalForm(empty_repl, empty_x);

    // Same normal form for:
    //
    // (= "" (str.replace x y (str.++ x x "A")))
    //
    // (and (= x "") (not (= y "")))
    Node empty_repl_xaa = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_STRREPL, x, y, xxa));
    Node empty_xy = d_nm->mkNode(
        kind::AND,
        d_nm->mkNode(kind::EQUAL, x, empty),
        d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, y, empty)));
    sameNormalForm(empty_repl_xaa, empty_xy);

    // (= "" (str.replace (str.++ x x "A") x y)) ---> false
    Node empty_repl_xxaxy = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_STRREPL, xxa, x, y));
    Node eq_xxa_repl = d_nm->mkNode(
        kind::EQUAL, xxa, d_nm->mkNode(kind::STRING_STRREPL, empty, y, x));
    sameNormalForm(empty_repl_xxaxy, f);

    // Same normal form for:
    //
    // (= "" (str.replace "A" x y))
    //
    // (= "A" (str.replace "" y x))
    Node empty_repl_axy = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_STRREPL, a, x, y));
    Node eq_a_repl = d_nm->mkNode(
        kind::EQUAL, a, d_nm->mkNode(kind::STRING_STRREPL, empty, y, x));
    sameNormalForm(empty_repl_axy, eq_a_repl);

    // Same normal form for:
    //
    // (= "" (str.replace x "A" ""))
    //
    // (str.prefix x "A")
    Node empty_repl_a = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_STRREPL, x, a, empty));
    Node prefix_a = d_nm->mkNode(kind::STRING_PREFIX, x, a);
    sameNormalForm(empty_repl_a, prefix_a);

    // Same normal form for:
    //
    // (= "" (str.substr x 1 2))
    //
    // (<= (str.len x) 1)
    Node empty_substr = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_SUBSTR, x, one, three));
    Node leq_len_x =
        d_nm->mkNode(kind::LEQ, d_nm->mkNode(kind::STRING_LENGTH, x), one);
    sameNormalForm(empty_substr, leq_len_x);

    // Different normal form for:
    //
    // (= "" (str.substr x 0 n))
    //
    // (<= n 0)
    Node empty_substr_x = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_SUBSTR, x, zero, n));
    Node leq_n = d_nm->mkNode(kind::LEQ, n, zero);
    differentNormalForms(empty_substr_x, leq_n);

    // Same normal form for:
    //
    // (= "" (str.substr "A" 0 n))
    //
    // (<= n 0)
    Node empty_substr_a = d_nm->mkNode(
        kind::EQUAL, empty, d_nm->mkNode(kind::STRING_SUBSTR, a, zero, n));
    sameNormalForm(empty_substr_a, leq_n);

    // Same normal form for:
    //
    // (= (str.++ x x a) (str.replace y (str.++ x x a) y))
    //
    // (= (str.++ x x a) y)
    Node eq_xxa_repl_y = d_nm->mkNode(
        kind::EQUAL, xxa, d_nm->mkNode(kind::STRING_STRREPL, y, xxa, y));
    Node eq_xxa_y = d_nm->mkNode(kind::EQUAL, xxa, y);
    sameNormalForm(eq_xxa_repl_y, eq_xxa_y);

    // (= (str.++ x x a) (str.replace (str.++ x x a) "A" "B")) ---> false
    Node eq_xxa_repl_xxa = d_nm->mkNode(
        kind::EQUAL, xxa, d_nm->mkNode(kind::STRING_STRREPL, xxa, a, b));
    sameNormalForm(eq_xxa_repl_xxa, f);

    // Same normal form for:
    //
    // (= (str.replace x "A" "B") "")
    //
    // (= x "")
    Node eq_repl = d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::STRING_STRREPL, x, a, b), empty);
    Node eq_x = d_nm->mkNode(kind::EQUAL, x, empty);
    sameNormalForm(eq_repl, eq_x);

    {
      // Same normal form for:
      //
      // (= (str.replace y "A" "B") "B")
      //
      // (= (str.replace y "B" "A") "A")
      Node lhs = d_nm->mkNode(
          kind::EQUAL, d_nm->mkNode(kind::STRING_STRREPL, x, a, b), b);
      Node rhs = d_nm->mkNode(
          kind::EQUAL, d_nm->mkNode(kind::STRING_STRREPL, x, b, a), a);
      sameNormalForm(lhs, rhs);
    }

    {
      // Same normal form for:
      //
      // (= (str.++ x "A" y) (str.++ "A" "A" (str.substr "AAA" 0 n)))
      //
      // (= (str.++ y x) (str.++ (str.substr "AAA" 0 n) "A"))
      Node lhs = d_nm->mkNode(
          kind::EQUAL,
          d_nm->mkNode(kind::STRING_CONCAT, x, a, y),
          d_nm->mkNode(kind::STRING_CONCAT,
                       a,
                       a,
                       d_nm->mkNode(kind::STRING_SUBSTR, aaa, zero, n)));
      Node rhs = d_nm->mkNode(
          kind::EQUAL,
          d_nm->mkNode(kind::STRING_CONCAT, x, y),
          d_nm->mkNode(kind::STRING_CONCAT,
                       d_nm->mkNode(kind::STRING_SUBSTR, aaa, zero, n),
                       a));
      sameNormalForm(lhs, rhs);
    }

    {
      // Same normal form for:
      //
      // (= (str.++ "A" x) "A")
      //
      // (= x "")
      Node lhs =
          d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::STRING_CONCAT, a, x), a);
      Node rhs = d_nm->mkNode(kind::EQUAL, x, empty);
      sameNormalForm(lhs, rhs);
    }

    {
      // (= (str.++ x "A") "") ---> false
      Node eq = d_nm->mkNode(
          kind::EQUAL, d_nm->mkNode(kind::STRING_CONCAT, x, a), empty);
      sameNormalForm(eq, f);
    }

    {
      // (= (str.++ x "B") "AAA") ---> false
      Node eq = d_nm->mkNode(
          kind::EQUAL, d_nm->mkNode(kind::STRING_CONCAT, x, b), aaa);
      sameNormalForm(eq, f);
    }

    {
      // (= (str.++ x "AAA") "A") ---> false
      Node eq = d_nm->mkNode(
          kind::EQUAL, d_nm->mkNode(kind::STRING_CONCAT, x, aaa), a);
      sameNormalForm(eq, f);
    }

    {
      // (= (str.++ "AAA" (str.substr "A" 0 n)) (str.++ x "B")) ---> false
      Node eq = d_nm->mkNode(
          kind::EQUAL,
          d_nm->mkNode(
              kind::STRING_CONCAT,
              aaa,
              d_nm->mkNode(kind::STRING_CONCAT,
                           a,
                           a,
                           d_nm->mkNode(kind::STRING_SUBSTR, x, zero, n))),
          d_nm->mkNode(kind::STRING_CONCAT, x, b));
      sameNormalForm(eq, f);
    }

    {
      // (= (str.++ "A" (int.to.str n)) "A") -/-> false
      Node eq = d_nm->mkNode(
          kind::EQUAL,
          d_nm->mkNode(
              kind::STRING_CONCAT, a, d_nm->mkNode(kind::STRING_ITOS, n)),
          a);
      differentNormalForms(eq, f);
    }

    {
      // (= (str.++ "A" x y) (str.++ x "B" z)) --> false
      Node eq = d_nm->mkNode(
          kind::EQUAL,
          d_nm->mkNode(kind::STRING_CONCAT, a, x, y),
          d_nm->mkNode(kind::STRING_CONCAT, x, b, z));
      sameNormalForm(eq, f);
    }

    {
      // (= (str.++ "B" x y) (str.++ x "AAA" z)) --> false
      Node eq = d_nm->mkNode(kind::EQUAL,
                             d_nm->mkNode(kind::STRING_CONCAT, b, x, y),
                             d_nm->mkNode(kind::STRING_CONCAT, x, aaa, z));
      sameNormalForm(eq, f);
    }

    {
      Node xrepl = d_nm->mkNode(kind::STRING_STRREPL, x, a, b);

      // Same normal form for:
      //
      // (= (str.++ "B" (str.replace x "A" "B") z y w)
      //    (str.++ z x "BA" z))
      //
      // (and (= (str.++ "B" (str.replace x "A" "B") z)
      //         (str.++ z x "B"))
      //      (= (str.++ y w) (str.++ "A" z)))
      Node lhs =
          d_nm->mkNode(kind::EQUAL,
                       d_nm->mkNode(kind::STRING_CONCAT, b, xrepl, z, y, w),
                       d_nm->mkNode(kind::STRING_CONCAT, z, x, ba, z));
      Node rhs = d_nm->mkNode(
          kind::AND,
          d_nm->mkNode(kind::EQUAL,
                       d_nm->mkNode(kind::STRING_CONCAT, b, xrepl, z),
                       d_nm->mkNode(kind::STRING_CONCAT, z, x, b)),
          d_nm->mkNode(kind::EQUAL,
                       d_nm->mkNode(kind::STRING_CONCAT, y, w),
                       d_nm->mkNode(kind::STRING_CONCAT, a, z)));
      sameNormalForm(lhs, rhs);
    }
  }

  void testStripConstantEndpoints()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node ab = d_nm->mkConst(::CVC4::String("AB"));
    Node abc = d_nm->mkConst(::CVC4::String("ABC"));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node bc = d_nm->mkConst(::CVC4::String("BC"));
    Node c = d_nm->mkConst(::CVC4::String("C"));
    Node cd = d_nm->mkConst(::CVC4::String("CD"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node n = d_nm->mkVar("n", intType);

    {
      // stripConstantEndpoints({ "" }, { "A" }, {}, {}, 0) ---> false
      std::vector<Node> n1 = {empty};
      std::vector<Node> n2 = {a};
      std::vector<Node> nb;
      std::vector<Node> ne;
      bool res = StringsEntail::stripConstantEndpoints(n1, n2, nb, ne, 0);
      TS_ASSERT(!res);
    }

    {
      // stripConstantEndpoints({ "A" }, { "A". (int.to.str n) }, {}, {}, 0)
      // ---> false
      std::vector<Node> n1 = {a};
      std::vector<Node> n2 = {a, d_nm->mkNode(kind::STRING_ITOS, n)};
      std::vector<Node> nb;
      std::vector<Node> ne;
      bool res = StringsEntail::stripConstantEndpoints(n1, n2, nb, ne, 0);
      TS_ASSERT(!res);
    }

    {
      // stripConstantEndpoints({ "ABCD" }, { "C" }, {}, {}, 1)
      // ---> true
      // n1 is updated to { "CD" }
      // nb is updated to { "AB" }
      std::vector<Node> n1 = {abcd};
      std::vector<Node> n2 = {c};
      std::vector<Node> nb;
      std::vector<Node> ne;
      std::vector<Node> n1r = {cd};
      std::vector<Node> nbr = {ab};
      bool res = StringsEntail::stripConstantEndpoints(n1, n2, nb, ne, 1);
      TS_ASSERT(res);
      TS_ASSERT_EQUALS(n1, n1r);
      TS_ASSERT_EQUALS(nb, nbr);
    }

    {
      // stripConstantEndpoints({ "ABC", x }, { "CD" }, {}, {}, 1)
      // ---> true
      // n1 is updated to { "C", x }
      // nb is updated to { "AB" }
      std::vector<Node> n1 = {abc, x};
      std::vector<Node> n2 = {cd};
      std::vector<Node> nb;
      std::vector<Node> ne;
      std::vector<Node> n1r = {c, x};
      std::vector<Node> nbr = {ab};
      bool res = StringsEntail::stripConstantEndpoints(n1, n2, nb, ne, 1);
      TS_ASSERT(res);
      TS_ASSERT_EQUALS(n1, n1r);
      TS_ASSERT_EQUALS(nb, nbr);
    }

    {
      // stripConstantEndpoints({ "ABC" }, { "A" }, {}, {}, -1)
      // ---> true
      // n1 is updated to { "A" }
      // nb is updated to { "BC" }
      std::vector<Node> n1 = {abc};
      std::vector<Node> n2 = {a};
      std::vector<Node> nb;
      std::vector<Node> ne;
      std::vector<Node> n1r = {a};
      std::vector<Node> ner = {bc};
      bool res = StringsEntail::stripConstantEndpoints(n1, n2, nb, ne, -1);
      TS_ASSERT(res);
      TS_ASSERT_EQUALS(n1, n1r);
      TS_ASSERT_EQUALS(ne, ner);
    }

    {
      // stripConstantEndpoints({ x, "ABC" }, { y, "A" }, {}, {}, -1)
      // ---> true
      // n1 is updated to { x, "A" }
      // nb is updated to { "BC" }
      std::vector<Node> n1 = {x, abc};
      std::vector<Node> n2 = {y, a};
      std::vector<Node> nb;
      std::vector<Node> ne;
      std::vector<Node> n1r = {x, a};
      std::vector<Node> ner = {bc};
      bool res = StringsEntail::stripConstantEndpoints(n1, n2, nb, ne, -1);
      TS_ASSERT(res);
      TS_ASSERT_EQUALS(n1, n1r);
      TS_ASSERT_EQUALS(ne, ner);
    }
  }

  void testRewriteMembership()
  {
    TypeNode strType = d_nm->stringType();

    std::vector<Node> vec_empty;
    Node abc = d_nm->mkConst(::CVC4::String("ABC"));
    Node re_abc = d_nm->mkNode(kind::STRING_TO_REGEXP, abc);
    Node x = d_nm->mkVar("x", strType);

    {
      // Same normal form for:
      //
      // (str.in.re x (re.++ (re.* re.allchar)
      //                     (re.* re.allchar)
      //                     (str.to.re "ABC")
      //                     (re.* re.allchar)))
      //
      // (str.contains x "ABC")
      Node sig_star = d_nm->mkNode(kind::REGEXP_STAR,
                                   d_nm->mkNode(kind::REGEXP_SIGMA, vec_empty));
      Node lhs = d_nm->mkNode(
          kind::STRING_IN_REGEXP,
          x,
          d_nm->mkNode(
              kind::REGEXP_CONCAT, sig_star, sig_star, re_abc, sig_star));
      Node rhs = d_nm->mkNode(kind::STRING_STRCTN, x, abc);
      sameNormalForm(lhs, rhs);
    }

    {
      // Different normal forms for:
      //
      // (str.in.re x (re.++ (re.* re.allchar) (str.to.re "ABC")))
      //
      // (str.contains x "ABC")
      Node sig_star = d_nm->mkNode(kind::REGEXP_STAR,
                                   d_nm->mkNode(kind::REGEXP_SIGMA, vec_empty));
      Node lhs =
          d_nm->mkNode(kind::STRING_IN_REGEXP,
                       x,
                       d_nm->mkNode(kind::REGEXP_CONCAT, sig_star, re_abc));
      Node rhs = d_nm->mkNode(kind::STRING_STRCTN, x, abc);
      differentNormalForms(lhs, rhs);
    }
  }

  void testRewriteRegexpConcat()
  {
    TypeNode strType = d_nm->stringType();

    std::vector<Node> emptyArgs;
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node allStar = d_nm->mkNode(kind::REGEXP_STAR,
                                d_nm->mkNode(kind::REGEXP_SIGMA, emptyArgs));
    Node xReg = d_nm->mkNode(kind::STRING_TO_REGEXP, x);
    Node yReg = d_nm->mkNode(kind::STRING_TO_REGEXP, y);

    {
      // In normal form:
      //
      // (re.++ (re.* re.allchar) (re.union (str.to.re x) (str.to.re y)))
      Node n = d_nm->mkNode(kind::REGEXP_CONCAT,
                            allStar,
                            d_nm->mkNode(kind::REGEXP_UNION, xReg, yReg));
      inNormalForm(n);
    }

    {
      // In normal form:
      //
      // (re.++ (str.to.re x) (re.* re.allchar))
      Node n = d_nm->mkNode(kind::REGEXP_CONCAT, xReg, allStar);
      inNormalForm(n);
    }
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;
  ExtendedRewriter* d_rewriter;

  NodeManager* d_nm;
};
