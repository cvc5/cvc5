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
inline std::shared_ptr<ProofNode> mkProof(Node n)
{
  return std::make_shared<ProofNode>(PfRule::ASSUME,
                                     std::vector<std::shared_ptr<ProofNode>>(),
                                     std::vector<Node>{n});
}
inline std::shared_ptr<ProofNode> mkProof(
    PfRule rule,
    std::initializer_list<std::shared_ptr<ProofNode>> children,
    std::initializer_list<Node> args = {})
{
  return std::make_shared<ProofNode>(
      rule, std::move(children), std::move(args));
}
inline std::shared_ptr<ProofNode> mkResolution(
    std::shared_ptr<ProofNode> clause, const std::vector<Node>& negLits)
{
  std::vector<std::shared_ptr<ProofNode>> children = {clause};
  for (const auto& n : negLits)
  {
    children.emplace_back(mkProof(n));
  }
  return std::make_shared<ProofNode>(
      PfRule::CHAIN_RESOLUTION, children, negLits);
}

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
  TNode d_parent;
  bool d_parentAssignment;

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
    // TODO: I guess we still need (or (not x)) => x
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
};

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

#endif
