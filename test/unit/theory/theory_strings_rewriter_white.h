/*********************                                                        */
/*! \file theory_strings_rewriter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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

  void testCheckEntailArithWithAssumption()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node x = d_nm->mkVar("x", intType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", intType);

    Node zero = d_nm->mkConst(Rational(0));

    Node slen_y = d_nm->mkNode(kind::STRING_LENGTH, y);
    Node x_plus_slen_y = d_nm->mkNode(kind::PLUS, x, slen_y);
    Node x_plus_slen_y_eq_zero =
        Rewriter::rewrite(d_nm->mkNode(kind::EQUAL, x_plus_slen_y, zero));

    // x + (str.len y) = 0 |= 0 >= x --> true
    TS_ASSERT(TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_slen_y_eq_zero, zero, x, false));

    // x + (str.len y) = 0 |= 0 > x --> false
    TS_ASSERT(!TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_slen_y_eq_zero, zero, x, true));

    Node x_plus_slen_y_plus_z_eq_zero = Rewriter::rewrite(d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::PLUS, x_plus_slen_y, z), zero));

    // x + (str.len y) + z = 0 |= 0 > x --> false
    TS_ASSERT(!TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_slen_y_plus_z_eq_zero, zero, x, true));

    Node x_plus_slen_y_plus_slen_y_eq_zero = Rewriter::rewrite(d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::PLUS, x_plus_slen_y, slen_y), zero));

    // x + (str.len y) + (str.len y) = 0 |= 0 >= x --> true
    TS_ASSERT(TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_slen_y_plus_slen_y_eq_zero, zero, x, false));

    Node five = d_nm->mkConst(Rational(5));
    Node six = d_nm->mkConst(Rational(6));
    Node x_plus_five = d_nm->mkNode(kind::PLUS, x, five);
    Node x_plus_five_lt_six =
        Rewriter::rewrite(d_nm->mkNode(kind::LT, x_plus_five, six));

    // x + 5 < 6 |= 0 >= x --> true
    TS_ASSERT(TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_five_lt_six, zero, x, false));

    // x + 5 < 6 |= 0 > x --> false
    TS_ASSERT(!TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_five_lt_six, zero, x, true));

    Node neg_x = d_nm->mkNode(kind::UMINUS, x);
    Node x_plus_five_lt_five =
        Rewriter::rewrite(d_nm->mkNode(kind::LT, x_plus_five, five));

    // x + 5 < 5 |= -x >= 0 --> true
    TS_ASSERT(TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_five_lt_five, neg_x, zero, false));

    // x + 5 < 5 |= 0 > x --> true
    TS_ASSERT(TheoryStringsRewriter::checkEntailArithWithAssumption(
        x_plus_five_lt_five, zero, x, false));
  }

  void testRewriteSubstr()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));

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

    // (str.substr "ABCD" (+ x 3) x) -> ""
    n = d_nm->mkNode(
        kind::STRING_SUBSTR, abcd, d_nm->mkNode(kind::PLUS, x, three), x);
    res = TheoryStringsRewriter::rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, empty);

    // (str.substr "ABCD" (+ x 2) x) -> (str.substr "ABCD" (+ x 2) x)
    n = d_nm->mkNode(
        kind::STRING_SUBSTR, abcd, d_nm->mkNode(kind::PLUS, x, two), x);
    res = TheoryStringsRewriter::rewriteSubstr(n);
    TS_ASSERT_EQUALS(res, n);
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
    Node res_repl_a = Rewriter::rewrite(repl_a);
    Node res_a_repl = Rewriter::rewrite(a_repl);
    TS_ASSERT_EQUALS(res_repl_a, res_a_repl);

    // Same normal form for:
    //
    // (str.++ y (str.replace "" x (str.substr y 0 3)) (str.substr y 0 3) "A" (str.substr y 0 3))
    //
    // (str.++ y (str.substr y 0 3) (str.replace "" x (str.substr y 0 3)) "A" (str.substr y 0 3))
    Node z = d_nm->mkNode(kind::STRING_SUBSTR, y, zero, three);
    Node repl_e_x_z = d_nm->mkNode(kind::STRING_STRREPL, empty, x, z);
    repl_a = d_nm->mkNode(kind::STRING_CONCAT, y, repl_e_x_z, z, a, z);
    a_repl = d_nm->mkNode(kind::STRING_CONCAT, y, z, repl_e_x_z, a, z);
    res_repl_a = Rewriter::rewrite(repl_a);
    res_a_repl = Rewriter::rewrite(a_repl);
    TS_ASSERT_EQUALS(res_repl_a, res_a_repl);

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
    Node res_a_substr_repl = Rewriter::rewrite(a_substr_repl);
    Node res_substr_repl_a = Rewriter::rewrite(substr_repl_a);
    TS_ASSERT_EQUALS(res_a_substr_repl, res_substr_repl_a);

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
    Node res_repl_substr_a = Rewriter::rewrite(repl_substr_a);
    Node res_a_repl_substr = Rewriter::rewrite(a_repl_substr);
    TS_ASSERT_EQUALS(res_repl_substr_a, res_a_repl_substr);
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
    Node res_concat1 = TheoryStringsRewriter::lengthPreserveRewrite(concat1);
    Node res_concat2 = TheoryStringsRewriter::lengthPreserveRewrite(concat2);
    TS_ASSERT_EQUALS(res_concat1, res_concat2);
  }

  void testRewriteIndexOf()
  {
    TypeNode strType = d_nm->stringType();

    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node abcd = d_nm->mkConst(::CVC4::String("ABCD"));
    Node aaad = d_nm->mkConst(::CVC4::String("AAAD"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node one = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));

    // Same normal form for:
    //
    // (str.to.int (str.indexof "A" x 1))
    //
    // (str.to.int (str.indexof "B" x 1))
    Node a_idof_x = d_nm->mkNode(kind::STRING_STRIDOF, a, x, one);
    Node itos_a_idof_x = d_nm->mkNode(kind::STRING_ITOS, a_idof_x);
    Node b_idof_x = d_nm->mkNode(kind::STRING_STRIDOF, b, x, one);
    Node itos_b_idof_x = d_nm->mkNode(kind::STRING_ITOS, b_idof_x);
    Node res_itos_a_idof_x = Rewriter::rewrite(itos_a_idof_x);
    Node res_itos_b_idof_x = Rewriter::rewrite(itos_b_idof_x);
    TS_ASSERT_EQUALS(res_itos_a_idof_x, res_itos_b_idof_x);

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
    Node res_idof_abcd = Rewriter::rewrite(idof_abcd);
    Node res_idof_aaad = Rewriter::rewrite(idof_aaad);
    TS_ASSERT_EQUALS(res_idof_abcd, res_idof_aaad);
  }

  void testRewriteReplace()
  {
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node c = d_nm->mkConst(::CVC4::String("C"));
    Node d = d_nm->mkConst(::CVC4::String("D"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", strType);

    // (str.replace "A" (str.replace "B", x, "C") "D") --> "A"
    Node repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                                  a,
                                  d_nm->mkNode(kind::STRING_STRREPL, b, x, c),
                                  d);
    Node res_repl_repl = Rewriter::rewrite(repl_repl);
    TS_ASSERT_EQUALS(res_repl_repl, a);

    // (str.replace "A" (str.replace "B", x, "A") "D") -/-> "A"
    repl_repl = d_nm->mkNode(kind::STRING_STRREPL,
                             a,
                             d_nm->mkNode(kind::STRING_STRREPL, b, x, a),
                             d);
    res_repl_repl = Rewriter::rewrite(repl_repl);
    TS_ASSERT_DIFFERS(res_repl_repl, a);

    // Same normal form for:
    //
    // (str.replace x (str.++ x y z) y)
    //
    // (str.replace x (str.++ x y z) z)
    Node xyz = d_nm->mkNode(kind::STRING_CONCAT, x, y, z);
    Node repl_x_xyz = d_nm->mkNode(kind::STRING_STRREPL, x, xyz, y);
    Node repl_x_zyx = d_nm->mkNode(kind::STRING_STRREPL, x, xyz, z);
    Node res_repl_x_xyz = Rewriter::rewrite(repl_x_xyz);
    Node res_repl_x_zyx = Rewriter::rewrite(repl_x_zyx);
    TS_ASSERT_EQUALS(res_repl_x_xyz, res_repl_x_zyx);

    // (str.replace "" (str.++ x x) x) --> ""
    Node repl_empty_xx = d_nm->mkNode(kind::STRING_STRREPL,
                                      empty,
                                      d_nm->mkNode(kind::STRING_CONCAT, x, x),
                                      x);
    Node res_repl_empty_xx = Rewriter::rewrite(repl_empty_xx);
    TS_ASSERT_EQUALS(res_repl_empty_xx, empty);

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
    Node res_repl_ab_xa_x = Rewriter::rewrite(repl_ab_xa_x);
    Node res_repl_ab_xa_e = Rewriter::rewrite(repl_ab_xa_e);
    TS_ASSERT_EQUALS(res_repl_ab_xa_x, res_repl_ab_xa_e);

    // (str.replace "AB" (str.++ x "A") x) -/-> (str.replace "AB" (str.++ "A" x)
    // "")
    Node repl_ab_ax_e = d_nm->mkNode(kind::STRING_STRREPL,
                                     d_nm->mkNode(kind::STRING_CONCAT, a, b),
                                     d_nm->mkNode(kind::STRING_CONCAT, a, x),
                                     empty);
    Node res_repl_ab_ax_e = Rewriter::rewrite(repl_ab_ax_e);
    TS_ASSERT_DIFFERS(res_repl_ab_xa_x, res_repl_ab_ax_e);
  }

  void testRewriteContains()
  {
    TypeNode strType = d_nm->stringType();

    Node empty = d_nm->mkConst(::CVC4::String(""));
    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node b = d_nm->mkConst(::CVC4::String("B"));
    Node c = d_nm->mkConst(::CVC4::String("C"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);
    Node z = d_nm->mkVar("z", strType);
    Node one = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));
    Node four = d_nm->mkConst(Rational(4));
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
    Node res_substr_3 = Rewriter::rewrite(substr_3);
    Node res_substr_4 = Rewriter::rewrite(substr_4);
    TS_ASSERT_EQUALS(res_substr_3, res_substr_4);

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
    Node res_concat_substr_3 = Rewriter::rewrite(concat_substr_3);
    Node res_concat_substr_4 = Rewriter::rewrite(concat_substr_4);
    TS_ASSERT_EQUALS(res_concat_substr_3, res_concat_substr_4);

    // (str.contains "A" (str.++ a (str.replace "B", x, "C")) --> false
    Node ctn_repl =
        d_nm->mkNode(kind::STRING_STRCTN,
                     a,
                     d_nm->mkNode(kind::STRING_CONCAT,
                                  a,
                                  d_nm->mkNode(kind::STRING_STRREPL, b, x, c)));
    Node res_ctn_repl = Rewriter::rewrite(ctn_repl);
    TS_ASSERT_EQUALS(res_ctn_repl, f);

    // (str.contains x (str.++ x x)) --> (= x "")
    Node x_cnts_x_x = d_nm->mkNode(
        kind::STRING_STRCTN, x, d_nm->mkNode(kind::STRING_CONCAT, x, x));
    Node res_x_cnts_x_x = Rewriter::rewrite(x_cnts_x_x);
    Node res_x_eq_empty =
        Rewriter::rewrite(d_nm->mkNode(kind::EQUAL, x, empty));
    TS_ASSERT_EQUALS(res_x_cnts_x_x, res_x_eq_empty);

    // Same normal form for:
    //
    // (str.contains (str.++ y x) (str.++ x z y))
    //
    // (and (str.contains (str.++ y x) (str.++ x y)) (= z ""))
    Node yx = d_nm->mkNode(kind::STRING_CONCAT, y, x);
    Node yx_cnts_xzy = d_nm->mkNode(
        kind::STRING_STRCTN, yx, d_nm->mkNode(kind::STRING_CONCAT, x, z, y));
    Node res_yx_cnts_xzy = Rewriter::rewrite(yx_cnts_xzy);
    Node xy = d_nm->mkNode(kind::STRING_CONCAT, x, y);
    Node yx_cnts_xy = d_nm->mkNode(kind::AND,
                                   d_nm->mkNode(kind::STRING_STRCTN, yx, xy),
                                   d_nm->mkNode(kind::EQUAL, z, empty));
    Node res_yx_cnts_xy = Rewriter::rewrite(yx_cnts_xy);
    TS_ASSERT_EQUALS(res_yx_cnts_xzy, res_yx_cnts_xy);
  }
};
