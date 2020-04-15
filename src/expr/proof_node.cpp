/*********************                                                        */
/*! \file proof_node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node utility
 **/

#include "expr/proof_node.h"

namespace CVC4 {

ProofNode::ProofNode(PfRule id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args)
{
  setValue(id, children, args);
}

PfRule ProofNode::getId() const { return d_id; }

const std::vector<std::shared_ptr<ProofNode>>& ProofNode::getChildren() const
{
  return d_children;
}

const std::vector<Node>& ProofNode::getArguments() const { return d_args; }

Node ProofNode::getResult() const { return d_proven; }

void ProofNode::getAssumptions(std::vector<Node>& assump) const
{
  std::unordered_set<const ProofNode*> visited;
  std::unordered_set<const ProofNode*>::iterator it;
  std::vector<const ProofNode*> visit;
  const ProofNode* cur;
  visit.push_back(this);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur->getId() == PfRule::ASSUME)
      {
        assump.push_back(cur->d_proven);
      }
      else
      {
        for (const std::shared_ptr<ProofNode>& cp : cur->d_children)
        {
          visit.push_back(cp.get());
        }
      }
    }
  } while (!visit.empty());
}

void ProofNode::setValue(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  d_id = id;
  d_children = children;
  d_args = args;
}

void ProofNode::printDebug(std::ostream& os) const
{
  os << "(" << d_id;
  for (const std::shared_ptr<ProofNode>& c : d_children)
  {
    os << " ";
    c->printDebug(os);
  }
  if (!d_args.empty())
  {
    os << " :args " << d_args;
  }
  os << ")";
}

}  // namespace CVC4
