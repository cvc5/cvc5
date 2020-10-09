/*********************                                                        */
/*! \file circuit_propagator_proofs.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proofs for the non-clausal circuit propagator.
 **
 ** Proofs for the non-clausal circuit propagator.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_PROOFS_H
#define CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_PROOFS_H

#include <memory>

#include "expr/node.h"
#include "expr/proof_node.h"
#include "theory/booleans/circuit_propagator.h"

namespace CVC4 {
namespace theory {
namespace booleans {

namespace {

template <typename T>
Node mkRat(T val)
{
  auto* nm = NodeManager::currentNM();
  return nm->mkConst<Rational>(val);
}

inline std::vector<Node> collectButHoldout(TNode parent,
                                           TNode::iterator holdout,
                                           bool negate = false)
{
  std::vector<Node> lits;
  for (TNode::iterator i = parent.begin(), i_end = parent.end(); i != i_end;
       ++i)
  {
    if (i != holdout)
    {
      lits.emplace_back(negate ? (*i).notNode() : Node(*i));
    }
  }
  return lits;
}

}  // namespace

struct CircuitPropagatorProver
{
  ProofNodeManager* d_pnm;
  EagerProofGenerator* d_epg;

  bool disabled() const { return d_pnm == nullptr; }

  std::shared_ptr<ProofNode> mkProof(Node n) { return d_pnm->mkAssume(n); }
  std::shared_ptr<ProofNode> mkProof(
      PfRule rule,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args = {})
  {
    return d_pnm->mkNode(rule, children, args);
  }
  std::shared_ptr<ProofNode> mkContra(const std::shared_ptr<ProofNode>& a,
                                      const std::shared_ptr<ProofNode>& b)
  {
    Assert(a->getResult().negate() == b->getResult());
    if (a->getResult().getKind() == Kind::NOT)
    {
      return mkProof(PfRule::CONTRA, {b, a});
    }
    return mkProof(PfRule::CONTRA, {a, b});
  }
  std::shared_ptr<ProofNode> mkResolution(std::shared_ptr<ProofNode> clause,
                                          const std::vector<Node>& lits)
  {
    std::vector<std::shared_ptr<ProofNode>> children = {clause};
    for (const auto& n : lits)
    {
      children.emplace_back(mkProof(n.notNode()));
    }
    return mkProof(PfRule::CHAIN_RESOLUTION, children, lits);
  }
  std::shared_ptr<ProofNode> mkNot(const std::shared_ptr<ProofNode>& n)
  {
    Node m = n->getResult();
    if (m.getKind() == Kind::NOT && m[0].getKind() == Kind::NOT)
    {
      return mkProof(PfRule::NOT_NOT_ELIM, {n});
    }
    return n;
  }

  std::shared_ptr<ProofNode> mkXorXFromY(bool negated, bool y, Node parent)
  {
    if (disabled()) return nullptr;
    if (y)
    {
      return mkResolution(
          mkProof(negated ? PfRule::NOT_XOR_ELIM1 : PfRule::XOR_ELIM2,
                  {mkProof(negated ? parent.notNode() : Node(parent))}),
          {parent[1].notNode()});
    }
    else
    {
      return mkResolution(
          mkProof(negated ? PfRule::NOT_XOR_ELIM2 : PfRule::XOR_ELIM1,
                  {mkProof(negated ? parent.notNode() : Node(parent))}),
          {parent[1]});
    }
  }
  std::shared_ptr<ProofNode> mkXorYFromX(bool negated, bool x, Node parent)
  {
    if (disabled()) return nullptr;
    if (x)
    {
      return mkResolution(
          mkProof(negated ? PfRule::NOT_XOR_ELIM2 : PfRule::XOR_ELIM1,
                  {mkProof(negated ? parent.notNode() : Node(parent))}),
          {parent[0].notNode()});
    }
    else
    {
      return mkResolution(
          mkProof(negated ? PfRule::NOT_XOR_ELIM1 : PfRule::XOR_ELIM2,
                  {mkProof(negated ? parent.notNode() : Node(parent))}),
          {parent[0]});
    }
  }
};

struct CircuitPropagatorBackwardProver : public CircuitPropagatorProver
{
  TNode d_parent;
  bool d_parentAssignment;

  CircuitPropagatorBackwardProver(ProofNodeManager* pnm,
                                  EagerProofGenerator* epg,
                                  TNode parent,
                                  bool parentAssignment)
      : CircuitPropagatorProver{pnm, epg},
        d_parent(parent),
        d_parentAssignment(parentAssignment)
  {
  }

  std::shared_ptr<ProofNode> andTrue(TNode::iterator i)
  {
    if (disabled()) return nullptr;
    return mkProof(
        PfRule::AND_ELIM, {mkProof(d_parent)}, {mkRat(i - d_parent.begin())});
  }
  std::shared_ptr<ProofNode> andFalse(TNode::iterator holdout)
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkResolution(mkProof(PfRule::NOT_AND, {mkProof(d_parent.notNode())}),
                     collectButHoldout(d_parent, holdout, true)));
  }

  std::shared_ptr<ProofNode> orFalse(TNode::iterator i)
  {
    if (disabled()) return nullptr;
    return mkNot(mkProof(PfRule::NOT_OR_ELIM,
                         {mkProof(d_parent.notNode())},
                         {mkRat(i - d_parent.begin())}));
  }
  std::shared_ptr<ProofNode> orTrue(TNode::iterator holdout)
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(d_parent),
                        collectButHoldout(d_parent, holdout));
  }

  std::shared_ptr<ProofNode> Not()
  {
    if (disabled()) return nullptr;
    return mkProof(d_parentAssignment ? Node(d_parent) : d_parent.notNode());
  }

  std::shared_ptr<ProofNode> iteC()
  {
    if (disabled()) return nullptr;
    if (d_parentAssignment)
    {
      return mkResolution(mkProof(PfRule::ITE_ELIM1, {mkProof(d_parent)}),
                          {d_parent[0].notNode()});
    }
    else
    {
      return mkResolution(
          mkProof(PfRule::NOT_ITE_ELIM1, {mkProof(d_parent.notNode())}),
          {d_parent[0]});
    }
  }
  std::shared_ptr<ProofNode> iteNotC()
  {
    if (disabled()) return nullptr;
    if (d_parentAssignment)
    {
      return mkResolution(mkProof(PfRule::ITE_ELIM2, {mkProof(d_parent)}),
                          {d_parent[0]});
    }
    else
    {
      return mkResolution(
          mkProof(PfRule::NOT_ITE_ELIM2, {mkProof(d_parent.notNode())}),
          {d_parent[0]});
    }
  }
  std::shared_ptr<ProofNode> iteIsX()
  {
    if (disabled()) return nullptr;
    // ITE c x y = v: if c is unassigned, x and y are assigned, x==v and y!=v,
    // assign(c = TRUE)
    if (d_parentAssignment)
    {
      // Resolve(ITE_ELIM2 (or c y), !y) = c
      return mkResolution(mkProof(PfRule::ITE_ELIM2, {mkProof(d_parent)}),
                          {d_parent[2]});
    }
    else
    {
      // Resolve(NOT_ITE_ELIM2 (or c !y), y) = c
      return mkResolution(
          mkProof(PfRule::NOT_ITE_ELIM2, {mkProof(d_parent.notNode())}),
          {d_parent[2]});
    }
  }
  std::shared_ptr<ProofNode> iteIsY()
  {
    if (disabled()) return nullptr;
    // ITE c x y = v: if c is unassigned, x and y are assigned, x!=v and y==v,
    // assign(c = FALSE)
    if (d_parentAssignment)
    {
      // Resolve(ITE_ELIM1 (or !c x), !x) = !c
      return mkResolution(mkProof(PfRule::ITE_ELIM1, {mkProof(d_parent)}),
                          {d_parent[1]});
    }
    else
    {
      // Resolve(NOT_ITE_ELIM2 (or !c !x), x) = !c
      return mkResolution(
          mkProof(PfRule::NOT_ITE_ELIM2, {mkProof(d_parent.notNode())}),
          {d_parent[1]});
    }
  }

  std::shared_ptr<ProofNode> eqXFromY(bool y)
  {
    if (disabled()) return nullptr;
    if (y)
    {
      return mkProof(
          PfRule::EQ_RESOLVE,
          {mkProof(d_parent[1]), mkProof(PfRule::SYMM, {mkProof(d_parent)})});
    }
    else
    {
      return mkNot(mkProof(PfRule::CHAIN_RESOLUTION,
                           {mkProof(PfRule::EQUIV_ELIM1, {mkProof(d_parent)}),
                            mkProof(d_parent[1].notNode())},
                           {d_parent[1]}));
    }
  }
  std::shared_ptr<ProofNode> eqYFromX(bool x)
  {
    if (disabled()) return nullptr;
    if (x)
    {
      return mkProof(PfRule::EQ_RESOLVE,
                     {mkProof(d_parent[0]), mkProof(d_parent)});
    }
    else
    {
      return mkNot(mkProof(PfRule::CHAIN_RESOLUTION,
                           {mkProof(PfRule::EQUIV_ELIM2, {mkProof(d_parent)}),
                            mkProof(d_parent[0].notNode())},
                           {d_parent[0]}));
    }
  }
  std::shared_ptr<ProofNode> neqXFromY(bool y)
  {
    // IFF x y = FALSE: if x [resp y] is assigned, assign(y = !x.assignment
    // [resp x = !y.assignment])
    if (y)
    {
      return mkResolution(
          mkProof(PfRule::NOT_EQUIV_ELIM2, {mkProof(d_parent.notNode())}),
          {d_parent[1].notNode()});
    }
    else
    {
      return mkResolution(
          mkProof(PfRule::NOT_EQUIV_ELIM1, {mkProof(d_parent.notNode())}),
          {d_parent[1]});
    }
  }
  std::shared_ptr<ProofNode> neqYFromX(bool x)
  {
    if (x)
    {
      return mkResolution(
          mkProof(PfRule::NOT_EQUIV_ELIM2, {mkProof(d_parent.notNode())}),
          {d_parent[0].notNode()});
    }
    else
    {
      return mkResolution(
          mkProof(PfRule::NOT_EQUIV_ELIM1, {mkProof(d_parent.notNode())}),
          {d_parent[0]});
    }
  }

  std::shared_ptr<ProofNode> impTrue()
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)}),
                        {d_parent[0].notNode()});
  }
  std::shared_ptr<ProofNode> impFalse()
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)}),
                        {d_parent[1]});
  }
  std::shared_ptr<ProofNode> impNegX()
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkProof(PfRule::NOT_IMPLIES_ELIM1, {mkProof(d_parent.notNode())}));
  }
  std::shared_ptr<ProofNode> impNegY()
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkProof(PfRule::NOT_IMPLIES_ELIM2, {mkProof(d_parent.notNode())}));
  }

  std::shared_ptr<ProofNode> xorX(bool x)
  {
    return mkXorYFromX(!d_parentAssignment, x, d_parent);
  }
  std::shared_ptr<ProofNode> xorY(bool y)
  {
    return mkXorXFromY(!d_parentAssignment, y, d_parent);
  }
};

struct CircuitPropagatorForwardProver : public CircuitPropagatorProver
{
  Node d_child;
  bool d_childAssignment;
  Node d_parent;

  CircuitPropagatorForwardProver(ProofNodeManager* pnm,
                                 EagerProofGenerator* epg,
                                 Node child,
                                 bool childAssignment,
                                 Node parent)
      : CircuitPropagatorProver{pnm, epg},
        d_child(child),
        d_childAssignment(childAssignment),
        d_parent(parent)
  {
  }

  std::shared_ptr<ProofNode> andTrue()
  {
    if (disabled()) return nullptr;
    std::vector<std::shared_ptr<ProofNode>> children;
    for (const auto& child : d_parent)
    {
      children.emplace_back(mkProof(child));
    }
    return mkProof(PfRule::AND_INTRO, children);
  }
  std::shared_ptr<ProofNode> andFalse(TNode::iterator holdout)
  {
    if (disabled()) return nullptr;
    // AND ...(x=TRUE)...: if all children BUT ONE now assigned to TRUE, and
    // AND == FALSE, assign(last_holdout = FALSE)
    return mkNot(
        mkResolution(mkProof(PfRule::NOT_AND, {mkProof(d_parent.notNode())}),
                     collectButHoldout(d_parent, holdout, true)));
  }
  std::shared_ptr<ProofNode> andFalse()
  {
    if (disabled()) return nullptr;
    auto it = std::find(d_parent.begin(), d_parent.end(), d_child);
    return mkProof(PfRule::SCOPE,
                   {mkContra(mkProof(PfRule::AND_ELIM,
                                     {mkProof(d_parent)},
                                     {mkRat(it - d_parent.begin())}),
                             mkProof(d_child.notNode()))},
                   {d_parent});
  }

  std::shared_ptr<ProofNode> orTrue()
  {
    if (disabled()) return nullptr;
    auto it = std::find(d_parent.begin(), d_parent.end(), d_child);
    return mkNot(mkProof(
        PfRule::CHAIN_RESOLUTION,
        {mkProof(
             PfRule::CNF_OR_NEG, {}, {d_parent, mkRat(it - d_parent.begin())}),
         mkProof(d_child)},
        {d_child.notNode()}));
  }
  std::shared_ptr<ProofNode> orTrue(TNode::iterator holdout)
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(d_parent),
                        collectButHoldout(d_parent, holdout));
  }
  std::shared_ptr<ProofNode> orFalse()
  {
    if (disabled()) return nullptr;
    std::vector<Node> children(d_parent.begin(), d_parent.end());
    return mkResolution(mkProof(PfRule::CNF_OR_POS, {}, {d_parent}), children);
  }

  std::shared_ptr<ProofNode> Not()
  {
    if (disabled()) return nullptr;
    return mkProof(d_childAssignment ? d_parent.notNode() : Node(d_parent));
  }

  std::shared_ptr<ProofNode> eqEval()
  {
    if (disabled()) return nullptr;
    if (d_childAssignment)
    {
      return mkProof(PfRule::CHAIN_RESOLUTION,
                     {mkProof(PfRule::CNF_EQUIV_NEG2, {}, {d_parent}),
                      mkProof(d_parent[0]),
                      mkProof(d_parent[1])},
                     {d_parent[0].notNode(), d_parent[1].notNode()});
    }
    else
    {
      return mkProof(PfRule::CHAIN_RESOLUTION,
                     {mkProof(PfRule::CNF_EQUIV_NEG1, {}, {d_parent}),
                      mkProof(d_parent[0].notNode()),
                      mkProof(d_parent[1].notNode())},
                     {d_parent[0], d_parent[1]});
    }
  }
  std::shared_ptr<ProofNode> eqYFromX()
  {
    if (disabled()) return nullptr;
    Assert(d_parent[0] == d_child);
    if (d_childAssignment)
    {
      return mkProof(PfRule::EQ_RESOLVE, {mkProof(d_child), mkProof(d_parent)});
    }
    else
    {
      return mkNot(mkProof(PfRule::CHAIN_RESOLUTION,
                           {mkProof(PfRule::EQUIV_ELIM2, {mkProof(d_parent)}),
                            mkProof(d_child.notNode())},
                           {d_child}));
    }
  }
  std::shared_ptr<ProofNode> neqYFromX()
  {
    if (disabled()) return nullptr;
    Assert(d_parent[0] == d_child);
    if (d_childAssignment)
    {
      return mkResolution(mkProof(PfRule::NOT_EQUIV_ELIM2, {mkProof(d_parent)}),
                          {d_child});
    }
    else
    {
      return mkResolution(mkProof(PfRule::NOT_EQUIV_ELIM1, {mkProof(d_parent)}),
                          {d_child.notNode()});
    }
  }
  std::shared_ptr<ProofNode> eqXFromY()
  {
    if (disabled()) return nullptr;
    Assert(d_parent[1] == d_child);
    if (d_childAssignment)
    {
      return mkProof(
          PfRule::EQ_RESOLVE,
          {mkProof(d_child), mkProof(PfRule::SYMM, {mkProof(d_parent)})});
    }
    else
    {
      return mkResolution(mkProof(PfRule::EQUIV_ELIM1, {mkProof(d_parent)}),
                          {d_child});
    }
  }
  std::shared_ptr<ProofNode> neqXFromY()
  {
    if (disabled()) return nullptr;
    Assert(d_parent[0] == d_child);
    if (d_childAssignment)
    {
      return mkResolution(mkProof(PfRule::NOT_EQUIV_ELIM2,
                                  {mkProof(PfRule::SYMM, {mkProof(d_parent)})}),
                          {d_child});
    }
    else
    {
      return mkResolution(mkProof(PfRule::NOT_EQUIV_ELIM1,
                                  {mkProof(PfRule::SYMM, {mkProof(d_parent)})}),
                          {d_child.notNode()});
    }
  }

  std::shared_ptr<ProofNode> impEval(bool premise, bool conclusion)
  {
    if (disabled()) return nullptr;
    if (!premise)
    {
      return mkResolution(mkProof(PfRule::CNF_IMPLIES_NEG1, {}, {d_parent}),
                          {d_parent[0]});
    }
    if (conclusion)
    {
      return mkResolution(mkProof(PfRule::CNF_IMPLIES_NEG2, {}, {d_parent}),
                          {d_parent[1].notNode()});
    }
    return mkResolution(mkProof(PfRule::CNF_IMPLIES_POS, {}, {d_parent}),
                        {d_parent[0].notNode(), d_parent[1]});
  }
  std::shared_ptr<ProofNode> impInverse()
  {
    if (disabled()) return nullptr;
    if (d_child == d_parent[0])
    {
      return mkResolution(mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)}),
                          {d_child.notNode()});
    }
    else
    {
      return mkNot(mkResolution(
          mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)}), {d_child}));
    }
  }
  std::shared_ptr<ProofNode> xorXFromY(bool negated)
  {
    return mkXorXFromY(negated, d_childAssignment, d_parent);
  }
  std::shared_ptr<ProofNode> xorYFromX(bool negated)
  {
    return mkXorYFromX(negated, d_childAssignment, d_parent);
  }
  };

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

#endif
