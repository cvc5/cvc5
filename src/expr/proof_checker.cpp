/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof checker
 **/

#include "expr/proof_checker.h"

namespace CVC4 {

Node ProofChecker::check(ProofNode* pn, Node expected)
{
  return check(pn->getRule(), pn->getChildren(), pn->getArguments(), expected);
}

Node ProofChecker::check(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  std::map<PfRule, ProofRuleChecker*>::iterator it = d_checker.find(id);
  if (it == d_checker.end())
  {
    // no checker for the rule
    Trace("pfcheck") << "ProofChecker::check: no checker for rule " << id
                     << std::endl;
    return Node::null();
  }
  // check it with the corresponding checker
  std::vector<Node> cchildren;
  for (const std::shared_ptr<ProofNode>& pc : children)
  {
    Assert(pc != nullptr);
    Node cres = pc->getResult();
    if (cres.isNull())
    {
      Trace("pfcheck")
          << "ProofChecker::check: child proof was invalid (null conclusion)"
          << std::endl;
      // should not have been able to create such a proof node
      Assert(false);
      return Node::null();
    }
    cchildren.push_back(cres);
  }
  Node res = it->second->check(id, cchildren, args);
  if (!expected.isNull() && res != expected)
  {
    Trace("pfcheck")
        << "ProofChecker::check: result does not match expected value."
        << std::endl;
    Trace("pfcheck") << "    result: " << res << std::endl;
    Trace("pfcheck") << "  expected: " << expected << std::endl;
    // it did not match the given expectation, fail
    return Node::null();
  }
  return res;
}

void ProofChecker::registerChecker(PfRule id, ProofRuleChecker* psc)
{
  std::map<PfRule, ProofRuleChecker*>::iterator it = d_checker.find(id);
  if (it != d_checker.end())
  {
    // checker is already provided
    Notice() << "ProofChecker::registerChecker: checker already exists for "
             << id << std::endl;
    return;
  }
  d_checker[id] = psc;
}

}  // namespace CVC4
