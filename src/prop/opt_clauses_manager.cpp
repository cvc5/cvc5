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
 * Implementation of lazy proof utility.
 */

#include "prop/opt_clauses_manager.h"

#include "proof/proof_node.h"

namespace cvc5 {
namespace prop {

OptimizedClausesManager::OptimizedClausesManager(
    context::Context* context,
    CDProof* parentProof,
    std::map<int, std::vector<std::shared_ptr<ProofNode>>>& optProofs)
    : context::ContextNotifyObj(context),
      d_context(context),
      d_optProofs(optProofs),
      d_parentProof(parentProof)
{
}

void OptimizedClausesManager::contextNotifyPop()
{
  int newLvl = d_context->getLevel();
  Trace("sat-proof") << "contextNotifyPop: called with lvl " << newLvl << "\n"
                     << push;
  // the increment is handled inside the loop, so that we can erase as we go
  for (auto it = d_optProofs.cbegin(); it != d_optProofs.cend();)
  {
    if (it->first <= newLvl)
    {
      Trace("sat-proof") << "Should re-add pfs of [" << it->first << "]:\n";
      for (const auto& pf : it->second)
      {
        Node processedPropgation = pf->getResult();
        Trace("sat-proof") << "\t- " << processedPropgation << "\n";
        Trace("sat-proof-debug") << "\t\t{" << pf << "} " << *pf.get() << "\n";
        // Note that this proof may have already been added in a previous
        // pop. For example, if a proof associated with level 1 was added
        // when going down from 2 to 1, but then we went up to 2 again, when
        // we go back to 1 the proof will still be there. Note that if say
        // we had a proof of level 1 that was added at level 2 when we were
        // going down from 3, we'd still need to add it again when going to
        // level 1, since it'd be popped in that case.
        if (!d_parentProof->hasStep(processedPropgation))
        {
          d_parentProof->addProof(pf);
        }
        else
        {
          Trace("sat-proof")
              << "\t..skipped since its proof was already added\n";
        }
      }
      ++it;
      continue;
    }
    if (Trace.isOn("sat-proof"))
    {
      Trace("sat-proof") << "Should remove from map pfs of [" << it->first
                         << "]:\n";
      for (const auto& pf : it->second)
      {
        Trace("sat-proof") << "\t- " << pf->getResult() << "\n";
      }
    }
    it = d_optProofs.erase(it);
  }
  Trace("sat-proof") << pop;
}

}  // namespace prop
}  // namespace cvc5
