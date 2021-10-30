/*********************                                                        */
/*! \file bool_proof_checker_black.h
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
  std::unique_ptr<ExprManager> d_em;
  NodeManager* d_nm;
  std::unique_ptr<SmtEngine> d_smt;
  ProofChecker* d_checker;

 public:
  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em.reset(new ExprManager);
    d_nm = NodeManager::fromExprManager(d_em.get());
    d_smt.reset(new SmtEngine(d_nm, &opts));
    d_smt->setOption("dag-thresh", "0");
    d_smt->setOption("proof", "true");
    d_smt->finishInit();
    // make a proof checker for booleans
    std::unique_ptr<booleans::BoolProofRuleChecker> bpfc(
        new booleans::BoolProofRuleChecker());
    d_checker = d_smt->getPfManager()->getProofNodeManager()->getChecker();
    bpfc->registerTo(d_checker);
  }

  void tearDown() override
  {
    d_smt.release();
    d_em.release();
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

    std::vector<Node> children{c1, c2, c3};
    std::vector<Node> args{d_nm->mkConst(true), l0, d_nm->mkConst(true), l1};
    // l0 v l0 v l0 v l1 v l2    ~l0    ~l1
    // ------------------------------------- CHAIN_RES_{T, l0, T, l1}
    //            l0 v l0 v l2
    //
    // where we want to test that the chain resolution checker is not
    // inadvertently removing more than one occurrence of the pivot.
    Node resChecker = d_checker->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
    TS_ASSERT(res == resChecker);

    c1Nodes.clear();
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l1.notNode());
    c1Nodes.push_back(l2);

    children.clear();
    children.push_back(d_nm->mkNode(kind::OR, c1Nodes));
    children.push_back(l0.notNode());
    children.push_back(l1);

    args.clear();
    args.push_back(d_nm->mkConst(true));
    args.push_back(l0);
    args.push_back(d_nm->mkConst(false));
    args.push_back(l1);
    // l0 v l0 v l0 v ~l1 v l2    ~l0    l1
    // ------------------------------------ CHAIN_RES_{T, l0, F, l1}
    //            l0 v l0 v l2
    //
    // where we test as above but with different polarites for the pivot.
    resChecker = d_checker->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
    TS_ASSERT(res == resChecker);
  }
};
