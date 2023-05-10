/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proofs for the non-clausal circuit propagator.
 */

#include "theory/booleans/proof_circuit_propagator.h"

#include <sstream>

#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace booleans {

namespace {

/** Shorthand to create a Node from a constant number */
template <typename T>
Node mkInt(T val)
{
  return NodeManager::currentNM()->mkConstInt(Rational(val));
}

/**
 * Collect all children from parent except for one particular child (the
 * "holdout"). The holdout is given as iterator, and should be an iterator into
 * the [parent.begin(),parent.end()] range.
 */
inline std::vector<Node> collectButHoldout(TNode parent,
                                           TNode::iterator holdout)
{
  std::vector<Node> lits;
  for (TNode::iterator i = parent.begin(), i_end = parent.end(); i != i_end;
       ++i)
  {
    if (i != holdout)
    {
      lits.emplace_back(*i);
    }
  }
  return lits;
}

}  // namespace

ProofCircuitPropagator::ProofCircuitPropagator(ProofNodeManager* pnm)
    : d_pnm(pnm)
{
}

bool ProofCircuitPropagator::disabled() const { return d_pnm == nullptr; }

std::shared_ptr<ProofNode> ProofCircuitPropagator::assume(Node n)
{
  return d_pnm->mkAssume(n);
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::conflict(
    const std::shared_ptr<ProofNode>& a, const std::shared_ptr<ProofNode>& b)
{
  if (a->getResult().notNode() == b->getResult())
  {
    return mkProof(PfRule::CONTRA, {a, b});
  }
  Assert(a->getResult() == b->getResult().notNode());
  return mkProof(PfRule::CONTRA, {b, a});
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::andFalse(
    Node parent, TNode::iterator holdout)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(
      mkCResolution(mkProof(PfRule::NOT_AND, {assume(parent.notNode())}),
                    collectButHoldout(parent, holdout),
                    false));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::orTrue(
    Node parent, TNode::iterator holdout)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkCResolution(
      assume(parent), collectButHoldout(parent, holdout), true);
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::Not(bool negate, Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(assume(negate ? Node(parent[0]) : parent));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::impliesXFromY(Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(mkResolution(
      mkProof(PfRule::IMPLIES_ELIM, {assume(parent)}), parent[1], true));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::impliesYFromX(Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkResolution(
      mkProof(PfRule::IMPLIES_ELIM, {assume(parent)}), parent[0], false);
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::eqXFromY(bool y, Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  if (y)
  {
    return mkProof(
        PfRule::EQ_RESOLVE,
        {assume(parent[1]), mkProof(PfRule::SYMM, {assume(parent)})});
  }
  return mkNot(mkResolution(
      mkProof(PfRule::EQUIV_ELIM1, {assume(parent)}), parent[1], true));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::eqYFromX(bool x, Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  if (x)
  {
    return mkProof(PfRule::EQ_RESOLVE, {assume(parent[0]), assume(parent)});
  }
  return mkNot(mkResolution(
      mkProof(PfRule::EQUIV_ELIM2, {assume(parent)}), parent[0], true));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::neqXFromY(bool y,
                                                             Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(mkResolution(
      mkProof(y ? PfRule::NOT_EQUIV_ELIM2 : PfRule::NOT_EQUIV_ELIM1,
              {assume(parent.notNode())}),
      parent[1],
      !y));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::neqYFromX(bool x,
                                                             Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(mkResolution(
      mkProof(x ? PfRule::NOT_EQUIV_ELIM2 : PfRule::NOT_EQUIV_ELIM1,
              {assume(parent.notNode())}),
      parent[0],
      !x));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::xorXFromY(bool negated,
                                                             bool y,
                                                             Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  if (y)
  {
    return mkNot(mkResolution(
        mkProof(negated ? PfRule::NOT_XOR_ELIM1 : PfRule::XOR_ELIM2,
                {assume(negated ? parent.notNode() : Node(parent))}),
        parent[1],
        false));
  }
  return mkNot(
      mkResolution(mkProof(negated ? PfRule::NOT_XOR_ELIM2 : PfRule::XOR_ELIM1,
                           {assume(negated ? parent.notNode() : Node(parent))}),
                   parent[1],
                   true));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::xorYFromX(bool negated,
                                                             bool x,
                                                             Node parent)
{
  if (disabled())
  {
    return nullptr;
  }
  if (x)
  {
    return mkNot(mkResolution(
        mkProof(negated ? PfRule::NOT_XOR_ELIM2 : PfRule::XOR_ELIM2,
                {assume(negated ? parent.notNode() : Node(parent))}),
        parent[0],
        false));
  }
  return mkNot(
      mkResolution(mkProof(negated ? PfRule::NOT_XOR_ELIM1 : PfRule::XOR_ELIM1,
                           {assume(negated ? parent.notNode() : Node(parent))}),
                   parent[0],
                   true));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::mkProof(
    PfRule rule,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  if (TraceIsOn("circuit-prop"))
  {
    std::stringstream ss;
    ss << "Constructing (" << rule;
    for (const auto& c : children)
    {
      ss << " " << *c;
    }
    if (!args.empty())
    {
      ss << " :args";
      for (const auto& a : args)
      {
        ss << " " << a;
      }
    }
    ss << ")";
    Trace("circuit-prop") << ss.str() << std::endl;
  }
  return d_pnm->mkNode(rule, children, args);
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::mkCResolution(
    const std::shared_ptr<ProofNode>& clause,
    const std::vector<Node>& lits,
    const std::vector<bool>& polarity)
{
  auto* nm = NodeManager::currentNM();
  std::vector<std::shared_ptr<ProofNode>> children = {clause};
  std::vector<Node> args;
  Assert(lits.size() == polarity.size());
  for (std::size_t i = 0, n = lits.size(); i < n; ++i)
  {
    bool pol = polarity[i];
    Node lit = lits[i];
    if (polarity[i])
    {
      if (lit.getKind() == Kind::NOT)
      {
        lit = lit[0];
        pol = !pol;
        children.emplace_back(assume(lit));
      }
      else
      {
        children.emplace_back(assume(lit.notNode()));
      }
    }
    else
    {
      children.emplace_back(assume(lit));
    }
    args.emplace_back(nm->mkConst(pol));
    args.emplace_back(lit);
  }
  return mkProof(PfRule::CHAIN_RESOLUTION, children, args);
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::mkCResolution(
    const std::shared_ptr<ProofNode>& clause,
    const std::vector<Node>& lits,
    bool polarity)
{
  return mkCResolution(clause, lits, std::vector<bool>(lits.size(), polarity));
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::mkResolution(
    const std::shared_ptr<ProofNode>& clause, const Node& lit, bool polarity)
{
  auto* nm = NodeManager::currentNM();
  if (polarity)
  {
    if (lit.getKind() == Kind::NOT)
    {
      return mkProof(PfRule::RESOLUTION,
                     {clause, assume(lit[0])},
                     {nm->mkConst(false), lit[0]});
    }
    return mkProof(PfRule::RESOLUTION,
                   {clause, assume(lit.notNode())},
                   {nm->mkConst(true), lit});
  }
  return mkProof(
      PfRule::RESOLUTION, {clause, assume(lit)}, {nm->mkConst(false), lit});
}

std::shared_ptr<ProofNode> ProofCircuitPropagator::mkNot(
    const std::shared_ptr<ProofNode>& n)
{
  Node m = n->getResult();
  if (m.getKind() == Kind::NOT && m[0].getKind() == Kind::NOT)
  {
    return mkProof(PfRule::NOT_NOT_ELIM, {n});
  }
  return n;
}

ProofCircuitPropagatorBackward::ProofCircuitPropagatorBackward(
    ProofNodeManager* pnm, TNode parent, bool parentAssignment)
    : ProofCircuitPropagator(pnm),
      d_parent(parent),
      d_parentAssignment(parentAssignment)
{
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorBackward::andTrue(
    TNode::iterator i)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkProof(
      PfRule::AND_ELIM, {assume(d_parent)}, {mkInt(i - d_parent.begin())});
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorBackward::orFalse(
    TNode::iterator i)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(mkProof(PfRule::NOT_OR_ELIM,
                       {assume(d_parent.notNode())},
                       {mkInt(i - d_parent.begin())}));
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorBackward::iteC(bool c)
{
  if (disabled())
  {
    return nullptr;
  }
  if (d_parentAssignment)
  {
    return mkResolution(
        mkProof(c ? PfRule::ITE_ELIM1 : PfRule::ITE_ELIM2, {assume(d_parent)}),
        d_parent[0],
        !c);
  }
  return mkNot(
      mkResolution(mkProof(c ? PfRule::NOT_ITE_ELIM1 : PfRule::NOT_ITE_ELIM2,
                           {assume(d_parent.notNode())}),
                   d_parent[0],
                   !c));
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorBackward::iteIsCase(unsigned c)
{
  if (disabled())
  {
    return nullptr;
  }
  if (d_parentAssignment)
  {
    return mkResolution(mkProof(c == 0 ? PfRule::ITE_ELIM1 : PfRule::ITE_ELIM2,
                                {assume(d_parent)}),
                        d_parent[c + 1],
                        true);
  }
  return mkResolution(
      mkProof(c == 0 ? PfRule::NOT_ITE_ELIM1 : PfRule::NOT_ITE_ELIM2,
              {assume(d_parent.notNode())}),
      d_parent[c + 1],
      false);
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorBackward::impliesNegX()
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(
      mkProof(PfRule::NOT_IMPLIES_ELIM1, {assume(d_parent.notNode())}));
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorBackward::impliesNegY()
{
  if (disabled())
  {
    return nullptr;
  }
  return mkNot(
      mkProof(PfRule::NOT_IMPLIES_ELIM2, {assume(d_parent.notNode())}));
}

ProofCircuitPropagatorForward::ProofCircuitPropagatorForward(
    ProofNodeManager* pnm, Node child, bool childAssignment, Node parent)
    : ProofCircuitPropagator{pnm},
      d_child(child),
      d_childAssignment(childAssignment),
      d_parent(parent)
{
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::andAllTrue()
{
  if (disabled())
  {
    return nullptr;
  }
  std::vector<std::shared_ptr<ProofNode>> children;
  for (const auto& child : d_parent)
  {
    children.emplace_back(assume(child));
  }
  return mkProof(PfRule::AND_INTRO, children);
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::andOneFalse()
{
  if (disabled())
  {
    return nullptr;
  }
  auto it = std::find(d_parent.begin(), d_parent.end(), d_child);
  return mkResolution(
      mkProof(
          PfRule::CNF_AND_POS, {}, {d_parent, mkInt(it - d_parent.begin())}),
      d_child,
      true);
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::orOneTrue()
{
  if (disabled())
  {
    return nullptr;
  }
  auto it = std::find(d_parent.begin(), d_parent.end(), d_child);
  return mkNot(mkResolution(
      mkProof(PfRule::CNF_OR_NEG, {}, {d_parent, mkInt(it - d_parent.begin())}),
      d_child,
      false));
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::orFalse()
{
  if (disabled())
  {
    return nullptr;
  }
  std::vector<Node> children(d_parent.begin(), d_parent.end());
  return mkCResolution(
      mkProof(PfRule::CNF_OR_POS, {}, {d_parent}), children, true);
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::iteEvalThen(bool x)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkCResolution(
      mkProof(x ? PfRule::CNF_ITE_NEG1 : PfRule::CNF_ITE_POS1, {}, {d_parent}),
      {d_parent[0], d_parent[1]},
      {false, !x});
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::iteEvalElse(bool y)
{
  if (disabled())
  {
    return nullptr;
  }
  return mkCResolution(
      mkProof(y ? PfRule::CNF_ITE_NEG2 : PfRule::CNF_ITE_POS2, {}, {d_parent}),
      {d_parent[0], d_parent[2]},
      {true, !y});
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::eqEval(bool x, bool y)
{
  if (disabled())
  {
    return nullptr;
  }
  if (x == y)
  {
    return mkCResolution(
        mkProof(x ? PfRule::CNF_EQUIV_NEG2 : PfRule::CNF_EQUIV_NEG1,
                {},
                {d_parent}),
        {d_parent[0], d_parent[1]},
        {!x, !y});
  }
  return mkCResolution(
      mkProof(
          x ? PfRule::CNF_EQUIV_POS1 : PfRule::CNF_EQUIV_POS2, {}, {d_parent}),
      {d_parent[0], d_parent[1]},
      {!x, !y});
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::impliesEval(
    bool premise, bool conclusion)
{
  if (disabled())
  {
    return nullptr;
  }
  if (!premise)
  {
    return mkResolution(
        mkProof(PfRule::CNF_IMPLIES_NEG1, {}, {d_parent}), d_parent[0], true);
  }
  if (conclusion)
  {
    return mkResolution(
        mkProof(PfRule::CNF_IMPLIES_NEG2, {}, {d_parent}), d_parent[1], false);
  }
  return mkCResolution(mkProof(PfRule::CNF_IMPLIES_POS, {}, {d_parent}),
                       {d_parent[0], d_parent[1]},
                       {false, true});
}

std::shared_ptr<ProofNode> ProofCircuitPropagatorForward::xorEval(bool x,
                                                                  bool y)
{
  if (disabled())
  {
    return nullptr;
  }
  if (x && y)
  {
    return mkCResolution(mkProof(PfRule::CNF_XOR_POS2, {}, {d_parent}),
                         {d_parent[0], d_parent[1]},
                         {false, false});
  }
  else if (x && !y)
  {
    return mkCResolution(mkProof(PfRule::CNF_XOR_NEG1, {}, {d_parent}),
                         {d_parent[0], d_parent[1]},
                         {false, true});
  }
  else if (!x && y)
  {
    return mkCResolution(mkProof(PfRule::CNF_XOR_NEG2, {}, {d_parent}),
                         {d_parent[0], d_parent[1]},
                         {true, false});
  }
  Assert(!x && !y);
  return mkCResolution(mkProof(PfRule::CNF_XOR_POS1, {}, {d_parent}),
                       {d_parent[0], d_parent[1]},
                       {true, true});
}

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal
