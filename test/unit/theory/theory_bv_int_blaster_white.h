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
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;

 public:
  TheoryBVIntBlastWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_nm);
    d_scope = new SmtScope(d_smt);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testBitblasterCore()
  {
    d_smt->setLogic("QF_BV");
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node x_plus_y = d_nm->mkNode(kind::BITVECTOR_PLUS, x, y);
    Node one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    Node x_shl_one = d_nm->mkNode(kind::BITVECTOR_SHL, x, one);
    Node eq = d_nm->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
    Node not_x_eq_y = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, x, y));
    d_smt->finishInit();
    IntBlaster* ib = new IntBlaster(d_smt, options::SolveBVAsIntMode::IAND);
    Node translation = ib->intBlastWithRanges(not_x_eq_y);
    std::cout << "original: " << not_x_eq_y << std::endl;
    std::cout << "translation: " << translation << std::endl;

    delete ib;
  }

}; /* class TheoryBVIntBlastWhite */
