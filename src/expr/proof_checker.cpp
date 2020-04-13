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
  ProofStep id = pn->d_id;
  Node res;
  std::map<ProofStep, ProofStepChecker*>::iterator it = d_checker.find(id);
  if (it != d_checker.end())
  {
    // check it with the corresponding checker
    res = it->second->check(id, pn->d_children, pn->d_args);
    if (!expected.isNull() && res!=expected)
    {
      // did not match expected
      res = Node::null();
    }
  }
  else
  {
    // no checker
  }
  pn->d_proven = res;
  return res;
}

void ProofChecker::registerChecker(ProofStep id, ProofStepChecker* psc)
{
  std::map<ProofStep, ProofStepChecker*>::iterator it = d_checker.find(id);
  if (it != d_checker.end())
  {
    // warning?
  }
  d_checker[id] = psc;
}

}  // namespace CVC4
