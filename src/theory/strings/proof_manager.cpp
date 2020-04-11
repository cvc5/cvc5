/*********************                                                        */
/*! \file strings_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of strings proof manager
 **/

#include "theory/strings/proof_manager.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {


bool ProofManager::registerStep(Node fact,
                                ProofStep id,
                                const std::vector<Node>& children,
                                const std::vector<Node>& args,
                                bool ensureChildren
                               )
{
  std::map<Node, std::unique_ptr<ProofNode> >::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end() && it->second->getId()!=ProofStep::ASSUME)
  {
    // already proven
    return true;
  }
  std::vector<ProofNode*> pchildren;
  for (const Node& c : children)
  {
    ProofNode* pc = getProof(c);
    if (pc == nullptr)
    {
      // failed to get a proof for child, fail
      if (ensureChildren)
      {
        return false;
      }
      // otherwise, we initialize it as an assumption
      std::vector<Node> pcargs = { c };
      std::vector<ProofNode*> pcassume;
      d_nodes[c].reset(new ProofNode(ProofStep::ASSUME, pcassume, pcargs));
    }
    pchildren.push_back(pc);
  }
  // create or reinitialize it
  if (it==d_nodes.end())
  {
    d_nodes[fact].reset(new ProofNode(id, pchildren, args));
  }
  else
  {
    d_nodes[fact]->initialize(id, pchildren,args);
  }
  Node pfact = d_nodes[fact]->getResult();
  // must be equal to given fact
  return fact == pfact;
}

ProofNode* ProofManager::getProof(Node fact) const
{
  std::map<Node, std::unique_ptr<ProofNode> >::const_iterator it =
      d_nodes.find(fact);
  if (it == d_nodes.end())
  {
    return nullptr;
  }
  return it->second.get();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
