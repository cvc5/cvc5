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
  return check(pn->getId(), pn->getChildren(), pn->getArguments(), expected);
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
    return Node::null();
  }
  // check it with the corresponding checker
  Node res = it->second->check(id, children, args);
  if (!expected.isNull() && res != expected)
  {
    return Node::null();
  }
  return res;
}

void ProofChecker::registerChecker(PfRule id, ProofRuleChecker* psc)
{
  std::map<PfRule, ProofRuleChecker*>::iterator it = d_checker.find(id);
  if (it != d_checker.end())
  {
    // warning?
  }
  d_checker[id] = psc;
}

}  // namespace CVC4
