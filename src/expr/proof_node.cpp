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
 ** \brief Implementation of proof node
 **/

#include "expr/proof_node.h"

namespace CVC4 {

ProofNode::ProofNode(ProofStep id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args) : d_id(id), d_children(children), d_args(args)
{
}

ProofStep ProofNode::getId() const { return d_id; }

Node ProofNode::getResult() const { return d_proven; }

Node ProofNode::applySubstitution(Node n, const std::vector<Node>& exp)
{
  Node curr = n;
  // apply substitution one at a time
  for (const Node& eqp : exp)
  {
    if (eqp.isNull() || eqp.getKind() != EQUAL)
    {
      return Node::null();
    }
    TNode var = eqp[0];
    TNode subs = eqp[1];
    curr = curr.substitute(var, subs);
  }
  return curr;
}

void ProofNode::getAssumptions(std::vector<Node>& assump)
{
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  visit.push_back(this);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur->getId() == ProofStep::ASSUME)
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

void ProofNode::printDebug(std::ostream& os) const
{
  // TODO
}

}  // namespace CVC4
