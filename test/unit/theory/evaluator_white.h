/*********************                                                        */
/*! \file evaluator_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <cxxtest/TestSuite.h>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"
#include "theory/theory_test_utils.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;

using namespace std;

class TheoryEvaluatorWhite : public CxxTest::TestSuite
{
  ExprManager *d_em;
  NodeManager *d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;

 public:
  TheoryEvaluatorWhite() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager;
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em, &opts);
    d_scope = new SmtScope(d_smt);
    d_smt->finalOptionsAreSet();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testSimple()
  {
    TypeNode bv64Type = d_nm->mkBitVectorType(64);

    Node w = d_nm->mkVar("w", bv64Type);
    Node x = d_nm->mkVar("x", bv64Type);
    Node y = d_nm->mkVar("y", bv64Type);
    Node z = d_nm->mkVar("z", bv64Type);

    Node zero = d_nm->mkConst(BitVector(64, (unsigned int)0));
    Node one = d_nm->mkConst(BitVector(64, (unsigned int)1));
    Node c1 = d_nm->mkConst(BitVector(
        64,
        (unsigned int)0b0000000100000101001110111001101000101110011101011011110011100111));
    Node c2 = d_nm->mkConst(BitVector(
        64,
        (unsigned int)0b0000000100000101001110111001101000101110011101011011110011100111));

    Node t = d_nm->mkNode(kind::ITE, d_nm->mkNode(kind::EQUAL, y, one), x, w);

    std::vector<Node> args = {w, x, y, z};
    std::vector<Node> vals = {c1, zero, one, c1};

    Evaluator eval;
    Node r = eval.eval(t, args, vals);
    TS_ASSERT_EQUALS(r,
                     Rewriter::rewrite(t.substitute(
                         args.begin(), args.end(), vals.begin(), vals.end())));
  }

  void testLoop()
  {
    TypeNode bv64Type = d_nm->mkBitVectorType(64);

    Node w = d_nm->mkBoundVar(bv64Type);
    Node x = d_nm->mkVar("x", bv64Type);

    Node zero = d_nm->mkConst(BitVector(1, (unsigned int)0));
    Node one = d_nm->mkConst(BitVector(64, (unsigned int)1));
    Node c = d_nm->mkConst(BitVector(
        64,
        (unsigned int)0b0001111000010111110000110110001101011110111001101100000101010100));

    Node largs = d_nm->mkNode(kind::BOUND_VAR_LIST, w);
    Node lbody = d_nm->mkNode(
        kind::BITVECTOR_CONCAT, bv::utils::mkExtract(w, 62, 0), zero);
    Node lambda = d_nm->mkNode(kind::LAMBDA, largs, lbody);
    Node t = d_nm->mkNode(kind::BITVECTOR_AND,
                          d_nm->mkNode(kind::APPLY_UF, lambda, one),
                          d_nm->mkNode(kind::APPLY_UF, lambda, x));

    std::vector<Node> args = {x};
    std::vector<Node> vals = {c};
    Evaluator eval;
    Node r = eval.eval(t, args, vals);
    TS_ASSERT_EQUALS(r,
                     Rewriter::rewrite(t.substitute(
                         args.begin(), args.end(), vals.begin(), vals.end())));
  }

  void testStrIdOf()
  {
    Node a = d_nm->mkConst(String("A"));
    Node empty = d_nm->mkConst(String(""));
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));

    std::vector<Node> args;
    std::vector<Node> vals;
    Evaluator eval;

    {
      Node n = d_nm->mkNode(kind::STRING_STRIDOF, a, empty, one);
      Node r = eval.eval(n, args, vals);
      TS_ASSERT_EQUALS(r, Rewriter::rewrite(n));
    }

    {
      Node n = d_nm->mkNode(kind::STRING_STRIDOF, a, a, one);
      Node r = eval.eval(n, args, vals);
      TS_ASSERT_EQUALS(r, Rewriter::rewrite(n));
    }

    {
      Node n = d_nm->mkNode(kind::STRING_STRIDOF, a, empty, two);
      Node r = eval.eval(n, args, vals);
      TS_ASSERT_EQUALS(r, Rewriter::rewrite(n));
    }

    {
      Node n = d_nm->mkNode(kind::STRING_STRIDOF, a, a, two);
      Node r = eval.eval(n, args, vals);
      TS_ASSERT_EQUALS(r, Rewriter::rewrite(n));
    }
  }

  void testCode()
  {
    Node a = d_nm->mkConst(String("A"));
    Node empty = d_nm->mkConst(String(""));

    std::vector<Node> args;
    std::vector<Node> vals;
    Evaluator eval;

    // (str.code "A") ---> 65
    {
      Node n = d_nm->mkNode(kind::STRING_TO_CODE, a);
      Node r = eval.eval(n, args, vals);
      TS_ASSERT_EQUALS(r, d_nm->mkConst(Rational(65)));
    }

    // (str.code "") ---> -1
    {
      Node n = d_nm->mkNode(kind::STRING_TO_CODE, empty);
      Node r = eval.eval(n, args, vals);
      TS_ASSERT_EQUALS(r, d_nm->mkConst(Rational(-1)));
    }
  }
};
