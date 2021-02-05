/*********************                                                        */
/*! \file theory_bv_int_blaster_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/int_blaster.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/theory_test_utils.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::smt;

using namespace std;

class TheoryBVIntBlastWhite : public CxxTest::TestSuite
{

 public:
  TheoryBVIntBlastWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_nm);
    d_smt->setOption("produce-models", CVC4::SExpr(true));
    d_scope = new SmtScope(d_smt);
    // d_smt->setLogic("QF_BV");
    d_smt->finishInit();
    d_true = d_nm->mkConst<bool>(true);
    d_one = d_nm->mkConst<Rational>(Rational(1));
  }

  void tearDown() override
  {
    d_true = Node::null();
    d_one = Node::null();

    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void printVector(std::vector<Node> vec)
  {
    for (Node v : vec)
    {
      std::cout << "  " << v << std::endl;
    }
  }

  void printMap(std::map<Node, Node> m)
  {
    map<Node, Node>::iterator it;
    for (it = m.begin(); it != m.end(); it++)
    {
      std::cout << "  " << it->first << " ====> " << it->second << std::endl;
    }
  }

  // a simple example
  // basically tests that there are no
  // internal assertion failures.
  void testExample()
  {
    // create an int blaster.
    // The constructor requires:
    // 1. A user context
    // 2. A translation mode (we chose IAND)
    // 3. A granularity (we chose 1)
    // 4. Whether to generate fresh integer variables
    IntBlaster* ib = new IntBlaster(
        d_smt->getUserContext(), options::SolveBVAsIntMode::IAND, 1, true);

    // create the formula:
    // ( x & y = x << 1) /\ ( x != y )
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_AND, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));
    Node formula = d_nm->mkNode(kind::AND, eq, not_x_eq_y);
    std::cout << "log" << std::endl;
    std::cout << "original formula: " << formula << std::endl;

    // prepare a vector of lemmas and a map for skolems
    vector<Node> lemmas;
    std::map<Node, Node> skolems;

    // perform the translation to integers
    Node translation = ib->intBlast(formula, lemmas, skolems);
    std::cout << "translated formula: " << translation << std::endl;
    std::cout << "lemmas: " << std::endl;
    printVector(lemmas);
    std::cout << "skolem definitions map: " << std::endl;
    printMap(skolems);

    // assert the translated formula to the smt engine.
    // also assert the generated lemmas
    d_smt->assertFormula(translation);
    d_smt->assertFormula(d_nm->mkAnd(lemmas));

    // check satisfiability of the translated formula
    Result r = d_smt->checkSat();
    // verify that it is SAT:
    TS_ASSERT(r.isSat());

    // get model values for x and y.
    // for that, we need to use the `skolems` map.
    // Note that we did not assert anything about x and y
    // in the smt engine.
    // skolems[x] and skolems[y] are their corresponding
    // terms, that we asserted about.
    Node x_value = d_smt->getValue(skolems[x]);
    Node y_value = d_smt->getValue(skolems[y]);
    std::cout << "get-value x: " << x_value << std::endl;
    std::cout << "get-value y: " << y_value << std::endl;

    delete ib;
  }

  // with fresh integer variables, we should be getting
  // range constraints
  void testLemmasWithFreshVars()
  {
    // an int-blaster that generates fresh Int variables 
    IntBlaster* ib = new IntBlaster(
        d_smt->getUserContext(), options::SolveBVAsIntMode::IAND, 1, true);

    // create the formula:
    // ( x & y = x << 1) /\ ( x != y )
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_AND, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));
    Node formula = d_nm->mkNode(kind::AND, eq, not_x_eq_y);

    // prepare a vector of lemmas and a map for skolems
    vector<Node> lemmas;
    std::map<Node, Node> skolems;

    // perform the translation to integers
    Node translation = ib->intBlast(formula, lemmas, skolems);

    // Make sure that:
    // 0. There are lemmas
    // 1. All lemmas are Boolean nodes
    // 2. All lemmas are conjunctions
    // 3. One literal is a Not >=, and the other is >=
    TS_ASSERT(lemmas.size() > 0);
    for (Node lemma : lemmas)
    {
      TS_ASSERT(lemma.getType().isBoolean());
      TS_ASSERT(lemma.getKind() == kind::AND);
      Node left = lemma[0];
      Node right = lemma[1];
      TS_ASSERT((left.getKind() == kind::GEQ && right.getKind() == kind::NOT
                 && right[0].getKind() == kind::GEQ)
                || (left.getKind() == kind::NOT
                    && left[0].getKind() == kind::GEQ
                    && right.getKind() == kind::GEQ));
    }
  }


  // without fresh integer variables, there are no lemmas.
  // The test is similar to testLemmasWithFreshVars,
  // but some TS_ASSERTs are different.
  void testLemmasWithoutFreshVars()
  {
    // an int-blaster that does not generate fresh Int variables 
    IntBlaster* ib = new IntBlaster(
        d_smt->getUserContext(), options::SolveBVAsIntMode::IAND, 1, false);

    // create the formula:
    // ( x & y = x << 1) /\ ( x != y )
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_AND, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));
    Node formula = d_nm->mkNode(kind::AND, eq, not_x_eq_y);

    // prepare a vector of lemmas and a map for skolems
    vector<Node> lemmas;
    std::map<Node, Node> skolems;

    // perform the translation to integers
    Node translation = ib->intBlast(formula, lemmas, skolems);

    // Make sure that there are no lemmas
    TS_ASSERT(lemmas.size() == 0);
  }


  // tests that SLTBV and ULTBV
  // work as expected
  void testSLTBVULTBV()
  {
    IntBlaster* ib = new IntBlaster(
        d_smt->getUserContext(), options::SolveBVAsIntMode::IAND, 1, true);

    // create the terms:
    // (slt x y), (sltbv x y), (ult x y), (ultbv x y)
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_slt_y = d_nm->mkNode(kind::BITVECTOR_SLT, x, y);
    Node x_sltbv_y = d_nm->mkNode(kind::BITVECTOR_SLTBV, x, y);
    Node x_ult_y = d_nm->mkNode(kind::BITVECTOR_ULT, x, y);
    Node x_ultbv_y = d_nm->mkNode(kind::BITVECTOR_ULTBV, x, y);

    // create lemmas and skolems.
    vector<Node> lemmas;
    std::map<Node, Node> skolems;

    // translate to integers
    Node int_x_slt_y = ib->intBlast(x_slt_y, lemmas, skolems);
    Node int_x_sltbv_y = ib->intBlast(x_sltbv_y, lemmas, skolems);
    Node int_x_ult_y = ib->intBlast(x_ult_y, lemmas, skolems);
    Node int_x_ultbv_y = ib->intBlast(x_ultbv_y, lemmas, skolems);

    // create equivalence assertions
    Node sltTrue = d_nm->mkNode(kind::EQUAL, int_x_slt_y, d_true);
    Node ultTrue = d_nm->mkNode(kind::EQUAL, int_x_ult_y, d_true);
    Node sltOne = d_nm->mkNode(kind::EQUAL, int_x_sltbv_y, d_one);
    Node ultOne = d_nm->mkNode(kind::EQUAL, int_x_ultbv_y, d_one);
    Node assertion1 = d_nm->mkNode(kind::DISTINCT, sltTrue, sltOne);
    Node assertion2 = d_nm->mkNode(kind::DISTINCT, ultTrue, ultOne);

    // asserting all range lemmas to the solver
    Node allLemmas = d_nm->mkAnd(lemmas);
    d_smt->assertFormula(allLemmas);

    Result r;

    // verifying that the translations of slt and sltbv are equivalent
    d_smt->push();
    d_smt->assertFormula(assertion1);
    r = d_smt->checkSat();
    std::cout << "result: " << r << std::endl;
    TS_ASSERT(r == Result::UNSAT);
    d_smt->pop();

    // verifying that the translations of ult and ultbv are equivalent
    d_smt->push();
    d_smt->assertFormula(assertion2);
    r = d_smt->checkSat();
    std::cout << "result: " << r << std::endl;
    TS_ASSERT(r == Result::UNSAT);
    d_smt->pop();

    delete ib;
  }

  // tests that the skolems include translations
  // back to bv from the fresh variables
  void testSkolemsWithFreshVars()
  {
    // an int-blaster that does introduces fresh Int variables
    IntBlaster* ib = new IntBlaster(
        d_smt->getUserContext(), options::SolveBVAsIntMode::IAND, 1, true);

    // create the formula:
    // ( x & y = x << 1) /\ ( x != y )
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_AND, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));
    Node formula = d_nm->mkNode(kind::AND, eq, not_x_eq_y);

    // prepare a vector of lemmas and a map for skolems
    vector<Node> lemmas;
    std::map<Node, Node> skolems;

    // perform the translation to integers
    Node translation = ib->intBlast(formula, lemmas, skolems);

    // verify that:
    // 1. each skolem is a bv variable
    // 2. The definition for each skolem is a nat2bv node
    map<Node, Node>::iterator it;
    for (it = skolems.begin(); it != skolems.end(); it++)
    {
      TS_ASSERT(it->first.isVar() && it->first.getType().isBitVector());
      unsigned bvsize = it->first.getType().getBitVectorSize();
      Node intToBVOp = d_nm->mkConst<IntToBitVector>(IntToBitVector(bvsize));
      TS_ASSERT(it->second.getOperator() == intToBVOp);
    }
  }

  // tests that the skolems are the BV variables
  // them selves, when no fresh Int variables
  // are introduced.
  // Similar to testSkolemsWithFreshVars, but
  // some TS_ASSERTs are different.
  void testSkolemsWithoutFreshVars()
  {
    // an int-blaster that does not introduce fresh Int variables
    IntBlaster* ib = new IntBlaster(
        d_smt->getUserContext(), options::SolveBVAsIntMode::IAND, 1, false);

    // create the formula:
    // ( x & y = x << 1) /\ ( x != y )
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_AND, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));
    Node formula = d_nm->mkNode(kind::AND, eq, not_x_eq_y);

    // prepare a vector of lemmas and a map for skolems
    vector<Node> lemmas;
    std::map<Node, Node> skolems;

    // perform the translation to integers
    Node translation = ib->intBlast(formula, lemmas, skolems);

    // verify that:
    // 1. each skolem is a bv variable
    // 2. The definition for each skolem itself.
    map<Node, Node>::iterator it;
    for (it = skolems.begin(); it != skolems.end(); it++)
    {
      TS_ASSERT(it->first.isVar() && it->first.getType().isBitVector());
      TS_ASSERT(it->second == it->first);
    }
  }
 protected:
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;
  Node d_true;
  Node d_one;

}; /* class TheoryBVIntBlastWhite */
