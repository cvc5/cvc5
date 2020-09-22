/*********************                                                        */
/*! \file theory_bv_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Mathias Preiner
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
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/bitblast/eager_bitblaster.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/theory.h"
#include "theory/theory_test_utils.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils; 
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::smt;

using namespace std;

class TheoryBVWhite : public CxxTest::TestSuite {

  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;

public:

  TheoryBVWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }
 
  void testBitblasterCore() {
    d_smt->setLogic("QF_BV");

    d_smt->setOption("bitblast", SExpr("eager"));
    d_smt->setOption("incremental", SExpr("false"));
    // Notice that this unit test uses the theory engine of a created SMT
    // engine d_smt. We must ensure that d_smt is properly initialized via
    // the following call, which constructs its underlying theory engine.
    d_smt->finishInit();
    TheoryBV* tbv = dynamic_cast<TheoryBV*>(
        d_smt->getTheoryEngine()->d_theoryTable[THEORY_BV]);
    BVSolverLazy* bvsl = dynamic_cast<BVSolverLazy*>(tbv->d_internal.get());
    EagerBitblaster* bb = new EagerBitblaster(bvsl, d_smt->getContext());

    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_PLUS, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));

    bb->bbFormula(eq);
    bb->bbFormula(not_x_eq_y);

    bool res = bb->solve();
    TS_ASSERT (res == false);
    delete bb;
  }

  void testMkUmulo() {
    d_smt->setOption("incremental", SExpr("true"));
    for (size_t w = 1; w < 16; ++w) {
      d_smt->push();
      Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(w));
      Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(w));

      Node zx = mkConcat(mkZero(w), x);
      Node zy = mkConcat(mkZero(w), y);
      Node mul = d_nm->mkNode(kind::BITVECTOR_MULT, zx, zy);
      Node lhs =
          d_nm->mkNode(kind::DISTINCT, mkExtract(mul, 2 * w - 1, w), mkZero(w));
      Node rhs = mkUmulo(x, y);
      Node eq = d_nm->mkNode(kind::DISTINCT, lhs, rhs);
      d_smt->assertFormula(eq.toExpr());
      Result res = d_smt->checkSat();
      TS_ASSERT(res.isSat() == Result::UNSAT);
      d_smt->pop();
    }
  }
};/* class TheoryBVWhite */
