/*********************                                                        */
/*! \file theory_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::theory::booleans::BoolProofRuleChecker
 **
 ** Black box testing of CVC4::theory::booleans::BoolProofRuleChecker
 **/

#include <cxxtest/TestSuite.h>

// Used in some of the tests
#include <sstream>
#include <vector>

#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/proof_checker.h"
#include "expr/proof_node_manager.h"
#include "expr/proof_rule.h"
#include "smt/proof_manager.h"
#include "smt/smt_engine.h"
#include "theory/booleans/proof_checker.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::smt;

class BoolProofCheckerBlack : public CxxTest::TestSuite
{
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  ProofChecker* d_checker;

 public:
  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager;
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em, &opts);
    d_smt->setOption("dag-thresh", "0");
    d_smt->setOption("proof-new", "true");
    d_smt->finishInit();
    // make a proof checker for booleans
    booleans::BoolProofRuleChecker* bpfc = new booleans::BoolProofRuleChecker();
    d_checker = d_smt->getPfManager()->getProofNodeManager()->getChecker();
    bpfc->registerTo(d_checker);
    delete bpfc;
  }

  void tearDown() override
  {
    delete d_smt;
    delete d_em;
  }

  void testChainResolution()
  {
    Node l0 = d_nm->mkVar("l0", d_nm->booleanType());
    Node l1 = d_nm->mkVar("l1", d_nm->booleanType());
    Node l2 = d_nm->mkVar("l2", d_nm->booleanType());
    Node l3 = d_nm->mkVar("l3", d_nm->booleanType());

    std::vector<Node> c1Nodes{l0, l0, l0, l1, l2};
    Node c1 = d_nm->mkNode(kind::OR, c1Nodes);
    Node c2 = l0.notNode();
    Node c3 = l1.notNode();

    // chain resolution with pivots l0, l1
    std::vector<Node> resNodes{l0, l0, l2};
    Node res = d_nm->mkNode(kind::OR, resNodes);
    // Node res = l2;

    std::vector<Node> children{c1, c2, c3};
    std::vector<Node> args{l0, l1};
    Node resChecker = d_checker->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
    TS_ASSERT(res == resChecker);
  }
};
