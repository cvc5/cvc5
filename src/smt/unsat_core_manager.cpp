/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the unsat core manager of SmtEngine.
 */

#include "unsat_core_manager.h"

#include "proof/proof_node_algorithm.h"
#include "smt/assertions.h"

namespace cvc5 {
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
    std::shared_ptr<ProofNode> pfn,
    std::map<Node, std::vector<std::vector<Node>>>& insts)
{
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;

  std::shared_ptr<ProofNode> cur;
  visit.push_back(pfn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur.get());
    if (it != visited.end())
    {
      continue;
    }
    visited[cur.get()] = true;
    const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
    if (cur->getRule() == PfRule::INSTANTIATE)
    {
      const std::vector<Node>& instTerms = cur->getArguments();
      Assert(cs.size() == 1);
      Node q = cs[0]->getResult();
      insts[q].push_back({instTerms.begin(), instTerms.end()});
    }
    for (const std::shared_ptr<ProofNode>& cp : cs)
    {
      visit.push_back(cp);
    }
  } while (!visit.empty());
}

}  // namespace smt
}  // namespace cvc5
