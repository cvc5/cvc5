/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Vinícius Braga Freire, Hans-Jörg
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node utility.
 */

#include "proof/proof_node.h"

#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_to_sexpr.h"

namespace cvc5::internal {

ProofNode::ProofNode(PfRule id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args)
    : d_provenChecked(false)
{
  setValue(id, children, args);
}

PfRule ProofNode::getRule() const { return d_rule; }

const std::vector<std::shared_ptr<ProofNode>>& ProofNode::getChildren() const
{
  return d_children;
}

const std::vector<Node>& ProofNode::getArguments() const { return d_args; }

Node ProofNode::getResult() const { return d_proven; }

bool ProofNode::isClosed()
{
  std::vector<Node> assumps;
  expr::getFreeAssumptions(this, assumps);
  return assumps.empty();
}

void ProofNode::setValue(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  d_rule = id;
  d_children = children;
  d_args = args;
}

void ProofNode::printDebug(std::ostream& os, bool printConclusion) const
{
  // convert to sexpr and print
  ProofNodeToSExpr pnts;
  Node ps = pnts.convertToSExpr(this, printConclusion);
  os << ps;
}

std::shared_ptr<ProofNode> ProofNode::clone() const
{
  std::unordered_map<const ProofNode*, std::shared_ptr<ProofNode>> visited;
  std::unordered_map<const ProofNode*, std::shared_ptr<ProofNode>>::iterator it;
  std::vector<const ProofNode*> visit;
  std::shared_ptr<ProofNode> cloned;
  visit.push_back(this);
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = nullptr;
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : children)
      {
        visit.push_back(cp.get());
      }
      continue;
    }
    visit.pop_back();
    if (it->second.get() == nullptr)
    {
      std::vector<std::shared_ptr<ProofNode>> cchildren;
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : children)
      {
        it = visited.find(cp.get());
        Assert(it != visited.end());
        // if we encounter nullptr here, then this child is currently being
        // traversed at a higher level, hence this corresponds to a cyclic
        // proof.
        if (it->second == nullptr)
        {
          Unreachable() << "Cyclic proof encountered when cloning a proof node";
        }
        cchildren.push_back(it->second);
      }
      cloned = std::make_shared<ProofNode>(
          cur->getRule(), cchildren, cur->getArguments());
      visited[cur] = cloned;
      // we trust the above cloning does not change what is proven
      cloned->d_proven = cur->d_proven;
      cloned->d_provenChecked = cur->d_provenChecked;
    }
  }
  Assert(visited.find(this) != visited.end());
  return visited[this];
}

std::ostream& operator<<(std::ostream& out, const ProofNode& pn)
{
  pn.printDebug(out);
  return out;
}

size_t ProofNodeHashFunction::operator()(const ProofNode* pfn) const
{
  uint64_t ret = fnv1a::offsetBasis;

  ret = fnv1a::fnv1a_64(ret, std::hash<Node>()(pfn->getResult()));
  ret = fnv1a::fnv1a_64(ret, static_cast<size_t>(pfn->getRule()));

  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const Pf& child : children)
  {
    ret = fnv1a::fnv1a_64(ret, std::hash<Node>()(child->getResult()));
  }

  const std::vector<Node>& args = pfn->getArguments();
  for (const Node& arg : args)
  {
    ret = fnv1a::fnv1a_64(ret, std::hash<Node>()(arg));
  }

  return static_cast<size_t>(ret);
}

}  // namespace cvc5::internal
