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
Node mkNot(Node n, bool negated) { return negated ? n.negate() : n; }

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

struct CircuitPropagatorProver
{
  ProofNodeManager* d_pnm;

  std::shared_ptr<ProofNode> mkProof(Node n) { return d_pnm->mkAssume(n); }
  std::shared_ptr<ProofNode> mkProof(
      PfRule rule,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args = {})
  {
    return d_pnm->mkNode(rule, children, args);
}
std::shared_ptr<ProofNode> mkResolution(
    std::shared_ptr<ProofNode> clause, const std::vector<Node>& negLits)
{
  std::vector<std::shared_ptr<ProofNode>> children = {clause};
  for (const auto& n : negLits)
  {
    children.emplace_back(mkProof(n));
  }
  return mkProof(PfRule::CHAIN_RESOLUTION, children, negLits);
}
};

struct CircuitPropagatorBackwardProver : public CircuitPropagatorProver
{
  TNode d_parent;
  bool d_parentAssignment;

  CircuitPropagatorBackwardProver(ProofNodeManager* pnm, TNode parent, bool parentAssignment):
    CircuitPropagatorProver{pnm}, d_parent(parent), d_parentAssignment(parentAssignment) {}

  std::shared_ptr<ProofNode> andTrue(TNode::iterator i)
  {
    return mkProof(
        PfRule::AND_ELIM, {mkProof(d_parent)}, {mkRat(i - d_parent.begin())});
  }
  std::shared_ptr<ProofNode> andFalse(TNode::iterator holdout)
  {
    // TODO: I guess we still need (or (not x)) => x
    return mkResolution(mkProof(PfRule::NOT_AND, {mkProof(d_parent.negate())}),
                        collectButHoldout(d_parent, holdout));
  }

  std::shared_ptr<ProofNode> orFalse(TNode::iterator i)
  {
    return mkProof(PfRule::NOT_OR_ELIM,
                   {mkProof(d_parent.negate())},
                   {mkRat(i - d_parent.begin())});
  }
  std::shared_ptr<ProofNode> orTrue(TNode::iterator holdout)
  {
    // TODO: I guess we still need (or x) => x
    return mkResolution(mkProof(d_parent),
                        collectButHoldout(d_parent, holdout));
  }

  std::shared_ptr<ProofNode> iteC()
  {
    if (d_parentAssignment)
    {
      return mkProof(PfRule::RESOLUTION,
                     {mkProof(PfRule::ITE_ELIM1, {mkProof(d_parent)}),
                      mkProof(d_parent[0])},
                     {d_parent[0]});
    }
    else
    {
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(PfRule::NOT_ITE_ELIM1, {mkProof(d_parent.negate())}),
           mkProof(d_parent[0])},
          {d_parent[0]});
    }
  }
  std::shared_ptr<ProofNode> iteNotC()
  {
    if (d_parentAssignment)
    {
      return mkProof(PfRule::RESOLUTION,
                     {mkProof(PfRule::ITE_ELIM2, {mkProof(d_parent)}),
                      mkProof(d_parent[0].negate())},
                     {d_parent[0]});
    }
    else
    {
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(PfRule::NOT_ITE_ELIM2, {mkProof(d_parent.negate())}),
           mkProof(d_parent[0].negate())},
          {d_parent[0]});
    }
  }
  std::shared_ptr<ProofNode> iteIsX()
  {
    // ITE c x y = v: if c is unassigned, x and y are assigned, x==v and y!=v,
    // assign(c = TRUE)
    if (d_parentAssignment)
    {
      // Resolve(ITE_ELIM2 (or c y), !y) = c
      return mkProof(PfRule::RESOLUTION,
                     {mkProof(PfRule::ITE_ELIM2, {mkProof(d_parent)}),
                      mkProof(d_parent[2].negate())},
                     {d_parent[2]});
    }
    else
    {
      // Resolve(NOT_ITE_ELIM2 (or c !y), y) = c
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(PfRule::NOT_ITE_ELIM2, {mkProof(d_parent.negate())}),
           mkProof(d_parent[2])},
          {d_parent[2]});
    }
  }
  std::shared_ptr<ProofNode> iteIsY()
  {
    // ITE c x y = v: if c is unassigned, x and y are assigned, x!=v and y==v,
    // assign(c = FALSE)
    if (d_parentAssignment)
    {
      // Resolve(ITE_ELIM1 (or !c x), !x) = !c
      return mkProof(PfRule::RESOLUTION,
                     {mkProof(PfRule::ITE_ELIM1, {mkProof(d_parent)}),
                      mkProof(d_parent[1].negate())},
                     {d_parent[1]});
    }
    else
    {
      // Resolve(NOT_ITE_ELIM2 (or !c !x), x) = !c
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(PfRule::NOT_ITE_ELIM2, {mkProof(d_parent.negate())}),
           mkProof(d_parent[1])},
          {d_parent[1]});
    }
  }

  std::shared_ptr<ProofNode> impTrue()
  {
    return mkProof(PfRule::RESOLUTION,
                   {mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)}),
                    mkProof(d_parent[0])},
                   {d_parent[0]});
  }
  std::shared_ptr<ProofNode> impFalse()
  {
    return mkProof(PfRule::RESOLUTION,
                   {mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)}),
                    mkProof(d_parent[1].negate())},
                   {d_parent[1]});
  }
  std::shared_ptr<ProofNode> impNeg(std::size_t i)
  {
    return mkProof(PfRule::NOT_OR_ELIM,
                   {mkProof(PfRule::IMPLIES_ELIM, {mkProof(d_parent)})},
                   {mkRat(i)});
  }

  std::shared_ptr<ProofNode> xorX(bool negated, bool x)
  {
    if (x)
    {
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(negated ? PfRule::NOT_XOR_ELIM2 : PfRule::XOR_ELIM2,
                   {mkProof(d_parent)}),
           mkProof(d_parent[0])},
          {d_parent[0]});
    }
    else
    {
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(negated ? PfRule::NOT_XOR_ELIM1 : PfRule::XOR_ELIM1,
                   {mkProof(d_parent)}),
           mkProof(d_parent[0].negate())},
          {d_parent[0]});
    }
  }
  std::shared_ptr<ProofNode> xorY(bool negated, bool y)
  {
    if (y)
    {
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(negated ? PfRule::NOT_XOR_ELIM2 : PfRule::XOR_ELIM2,
                   {mkProof(d_parent)}),
           mkProof(d_parent[1])},
          {d_parent[1]});
    }
    else
    {
      return mkProof(
          PfRule::RESOLUTION,
          {mkProof(negated ? PfRule::NOT_XOR_ELIM1 : PfRule::XOR_ELIM1,
                   {mkProof(d_parent)}),
           mkProof(d_parent[1].negate())},
          {d_parent[1]});
    }
  }
};

  struct CircuitPropagatorForwardProver : public CircuitPropagatorProver
  {
    Node d_child;
    bool d_childAssignment;
    Node d_parent;

    CircuitPropagatorForwardProver(ProofNodeManager* pnm, Node child, bool childAssignment, Node parent):
    CircuitPropagatorProver{pnm}, d_child(child), d_childAssignment(childAssignment), d_parent(parent) {}

    std::shared_ptr<ProofNode> andTrue()
    {
      std::vector<std::shared_ptr<ProofNode>> children;
      for (const auto& child : d_parent)
      {
        children.emplace_back(mkProof(child));
      }
      return mkProof(PfRule::AND_INTRO, children);
    }
    std::shared_ptr<ProofNode> andFalse()
    {
      auto it = std::find(d_parent.begin(), d_parent.end(), d_child);
      return mkProof(PfRule::SCOPE,
                     {mkProof(PfRule::CONTRA,
                              {mkProof(PfRule::AND_ELIM,
                                       {mkProof(d_parent)},
                                       {mkRat(it - d_parent.begin())}),
                               mkProof(d_child.negate())})},
                     {d_parent});
    }

    std::shared_ptr<ProofNode> orTrue()
    {
      auto it = std::find(d_parent.begin(), d_parent.end(), d_child);
      return mkProof(PfRule::RESOLUTION,
                     {mkProof(PfRule::CNF_OR_NEG,
                              {},
                              {d_parent, mkRat(it - d_parent.begin())}),
                      mkProof(d_child)},
                     {d_child});
    }
    std::shared_ptr<ProofNode> orFalse()
    {
      std::vector<Node> children(d_parent.begin(), d_parent.end());
      return mkResolution(mkProof(PfRule::CNF_OR_POS, {}, {d_parent}),
                          children);
    }
    std::shared_ptr<ProofNode> eqYFromX()
    {
      Assert(d_parent[0] == d_child);
      return mkProof(PfRule::EQ_RESOLVE,
                     {mkProof(d_childAssignment ? d_child.negate() : d_child),
                      mkProof(d_parent)});
    }
    std::shared_ptr<ProofNode> neqYFromX()
    {
      Assert(d_parent[0] == d_child);
      if (d_childAssignment)
      {
        return mkResolution(
            mkProof(PfRule::NOT_EQUIV_ELIM2, {mkProof(d_parent)}), {d_child});
      }
      else
      {
        return mkResolution(
            mkProof(PfRule::NOT_EQUIV_ELIM1, {mkProof(d_parent)}),
            {d_child.negate()});
      }
    }
    std::shared_ptr<ProofNode> eqXFromY()
    {
      Assert(d_parent[1] == d_child);
      return mkProof(PfRule::EQ_RESOLVE,
                     {mkProof(d_childAssignment ? d_child.negate() : d_child),
                      mkProof(PfRule::SYMM, {mkProof(d_parent)})});
    }
    std::shared_ptr<ProofNode> neqXFromY()
    {
      Assert(d_parent[0] == d_child);
      if (d_childAssignment)
      {
        return mkResolution(
            mkProof(PfRule::NOT_EQUIV_ELIM2,
                    {mkProof(PfRule::SYMM, {mkProof(d_parent)})}),
            {d_child});
      }
      else
      {
        return mkResolution(
            mkProof(PfRule::NOT_EQUIV_ELIM1,
                    {mkProof(PfRule::SYMM, {mkProof(d_parent)})}),
            {d_child.negate()});
      }
    }

    std::shared_ptr<ProofNode> impEval(bool premise, bool conclusion)
    {
      return nullptr;
    }
  };

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

#endif
