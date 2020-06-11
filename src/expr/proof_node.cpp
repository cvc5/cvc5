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

#include "expr/proof_node_to_sexpr.h"

namespace CVC4 {

ProofNode::ProofNode(PfRule id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args)
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

void ProofNode::getFreeAssumptions(std::vector<Node>& assump)
{
  std::map<Node, std::vector<ProofNode*>> amap;
  getFreeAssumptionsMap(amap);
  for (const std::pair<const Node, std::vector<ProofNode*>>& p : amap)
  {
    assump.push_back(p.first);
  }
}

void ProofNode::getFreeAssumptionsMap(
    std::map<Node, std::vector<ProofNode*>>& amap)
{
  // proof should not be cyclic
  // visited set false after preorder traversal, true after postorder traversal
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<ProofNode*> visit;
  // Maps a bound assumption to the number of bindings it is under
  // e.g. in (SCOPE (SCOPE (ASSUME x) (x y)) (y)), y would be mapped to 2 at
  // (ASSUME x), and x would be mapped to 1.
  //
  // This map is used to track which nodes are in scope while traversing the
  // DAG. The in-scope assumptions are keys in the map. They're removed when
  // their binding count drops to zero. Let's annotate the above example to
  // serve as an illustration:
  //
  //   (SCOPE0 (SCOPE1 (ASSUME x) (x y)) (y))
  //
  // This is how the map changes during the traversal:
  //   after  previsiting SCOPE0: { y: 1 }
  //   after  previsiting SCOPE1: { y: 2, x: 1 }
  //   at                 ASSUME: { y: 2, x: 1 } (so x is in scope!)
  //   after postvisiting SCOPE1: { y: 1 }
  //   after postvisiting SCOPE2: {}
  //
  std::unordered_map<Node, uint32_t, NodeHashFunction> scopeDepth;
  ProofNode* cur;
  visit.push_back(this);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = true;
      PfRule id = cur->getRule();
      if (id == PfRule::ASSUME)
      {
        Assert(cur->d_args.size() == 1);
        Node f = cur->d_args[0];
        if (!scopeDepth.count(f))
        {
          amap[f].push_back(cur);
        }
      }
      else
      {
        if (id == PfRule::SCOPE)
        {
          // mark that its arguments are bound in the current scope
          for (const Node& a : cur->d_args)
          {
            scopeDepth[a] += 1;
          }
          // will need to unbind the variables below
          visited[cur] = false;
        }
        // The following loop cannot be merged with the loop above because the
        // same subproof
        for (const std::shared_ptr<ProofNode>& cp : cur->d_children)
        {
          visit.push_back(cp.get());
        }
      }
    }
    else if (!it->second)
    {
      Assert(cur->getRule() == PfRule::SCOPE);
      // unbind its assumptions
      for (const Node& a : cur->d_args)
      {
        auto scopeCt = scopeDepth.find(a);
        Assert(scopeCt != scopeDepth.end());
        scopeCt->second -= 1;
        if (scopeCt->second == 0)
        {
          scopeDepth.erase(scopeCt);
        }
      }
    }
  } while (!visit.empty());
}

bool ProofNode::isClosed()
{
  std::vector<Node> assumps;
  getFreeAssumptions(assumps);
  return assumps.empty();
}

std::shared_ptr<ProofNode> ProofNode::clone() const
{
  std::vector<std::shared_ptr<ProofNode>> cchildren;
  for (const std::shared_ptr<ProofNode>& cp : d_children)
  {
    cchildren.push_back(cp->clone());
  }
  std::shared_ptr<ProofNode> thisc =
      std::make_shared<ProofNode>(d_rule, cchildren, d_args);
  thisc->d_proven = d_proven;
  return thisc;
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

void ProofNode::printDebug(std::ostream& os) const
{
  // convert to sexpr and print
  ProofNodeToSExpr pnts;
  Node ps = pnts.convertToSExpr(this);
  os << ps;
}

}  // namespace CVC4
