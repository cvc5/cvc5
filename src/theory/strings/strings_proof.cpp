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
 ** \brief Implementation of strings proof
 **/

#include "theory/strings/strings_proof.h"

namespace CVC4 {
namespace theory {
namespace strings {

const char* toString(ProofStep i)
{
  switch (i)
  {
    case ProofStep::SUBSTITUTE: return "SUBSTITUTE";
    case ProofStep::REWRITE: return "REWRITE";
    case ProofStep::REFL: return "REFL";
    case ProofStep::SYMM: return "SYMM";
    case ProofStep::TRANS: return "TRANS";
    case ProofStep::CONG: return "CONG";
    case ProofStep::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofStep i)
{
  out << toString(i);
  return out;
}

ProofNode::ProofNode( ProofStep id, const std::vector<ProofNode*>& children, const std::vector<Node>& args)
: d_id(id), d_children(children), d_args(args){
}

Node ProofNode::computeResult()
{
  // TODO
  return d_proven;
}

void ProofNode::printDebug(std::ostream& os) const
{
  // TODO
}

bool ProofManager::registerStep( Node fact, ProofStep id, const std::vector<Node>& children, const std::vector<Node>& args)
{
  std::map< Node, std::unique_ptr<ProofNode> >::iterator it = d_nodes.find(fact);
  if (it!=d_nodes.end())
  {
    // already proven
    return true;
  }
  std::vector<ProofNode*> pchildren;
  for (const Node& c : children)
  {
    ProofNode * pc = getProof(c);
    if (pc==nullptr)
    {
      return false;
    }
    pchildren.push_back(pc);
  }
  d_nodes[fact].reset(new ProofNode(id, pchildren, args));
  Node pfact = d_nodes[fact]->computeResult();
  return fact==pfact;
}

ProofNode * ProofManager::getProof(Node fact) const
{
  std::map< Node, std::unique_ptr<ProofNode> >::const_iterator it = d_nodes.find(fact);
  if (it==d_nodes.end())
  {
    return nullptr;
  }
  return it->second.get();
}
  
}  // namespace strings
}  // namespace theory
}  // namespace CVC4
