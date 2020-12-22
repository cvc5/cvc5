/*********************                                                        */
/*! \file unsat_core_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the unsat core manager of SmtEngine.
 **/

#include "unsat_core_manager.h"

#include "expr/proof_node_algorithm.h"
#include "smt/assertions.h"

namespace CVC4 {
namespace smt {

void UnsatCoreManager::getUnsatCore(std::shared_ptr<ProofNode> pfn,
                                    Assertions& as,
                                    std::vector<Node>& core)
{
  Trace("unsat-core") << "UCManager::getUnsatCore: final proof: " << *pfn.get()
                      << "\n";
  Assert(pfn->getRule() == PfRule::SCOPE);
  std::vector<Node> fassumps;
  expr::getFreeAssumptions(pfn->getChildren()[0].get(), fassumps);
  Trace("unsat-core") << "UCManager::getUnsatCore: free assumptions: "
                      << fassumps << "\n";
  context::CDList<Node>* al = as.getAssertionList();
  Assert(al != nullptr);
  for (context::CDList<Node>::const_iterator i = al->begin(); i != al->end();
       ++i)
  {
    Trace("unsat-core") << "is assertion " << *i << " there?\n";
    if (std::find(fassumps.begin(), fassumps.end(), *i) != fassumps.end())
    {
      Trace("unsat-core") << "\tyes\n";
      core.push_back(*i);
    }
  }
  if (Trace.isOn("unsat-core"))
  {
    Trace("unsat-core") << "UCManager::getUnsatCore():\n";
    for (const Node& n : core)
    {
      Trace("unsat-core") << "- " << n << "\n";
    }
  }
}

void UnsatCoreManager::getRelevantInstantiations(
    std::shared_ptr<ProofNode> pfn, std::map<Node, std::vector<Node>>& insts)
{
}

}  // namespace smt
}  // namespace CVC4
