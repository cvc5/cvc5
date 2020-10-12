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
    if (Trace.isOn("circuit-prop"))
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
  std::shared_ptr<ProofNode> mkContra(const std::shared_ptr<ProofNode>& a,
                                      const std::shared_ptr<ProofNode>& b)
  {
    if (a->getResult().notNode() == b->getResult())
    {
      return mkProof(PfRule::CONTRA, {a, b});
    }
    Assert(a->getResult() == b->getResult().notNode());
    return mkProof(PfRule::CONTRA, {b, a});
  }
  std::shared_ptr<ProofNode> mkResolution(std::shared_ptr<ProofNode> clause,
                                          const std::vector<Node>& lits)
  {
    std::vector<std::shared_ptr<ProofNode>> children = {clause};
    for (const auto& n : lits)
    {
      children.emplace_back(mkProof(n.negate()));
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

  /** (and true ... holdout true ...)  -->  holdout */
  std::shared_ptr<ProofNode> andFalse(Node parent, TNode::iterator holdout)
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkResolution(mkProof(PfRule::NOT_AND, {mkProof(parent.notNode())}),
                     collectButHoldout(parent, holdout, true)));
  }

  /** (or false ... holdout false ...)  ->  holdout */
  std::shared_ptr<ProofNode> orTrue(Node parent, TNode::iterator holdout)
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(parent), collectButHoldout(parent, holdout));
  }

  /** (=> X false)  -->  (not X) */
  std::shared_ptr<ProofNode> impliesXFromY(Node parent)
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(PfRule::IMPLIES_ELIM, {mkProof(parent)}),
                        {parent[1]});
  }
  /** (=> true Y)  -->  Y */
  std::shared_ptr<ProofNode> impliesYFromX(Node parent)
  {
    if (disabled()) return nullptr;
    return mkResolution(mkProof(PfRule::IMPLIES_ELIM, {mkProof(parent)}),
                        {parent[0].notNode()});
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

  /** and true  -->  child is true */
  std::shared_ptr<ProofNode> andTrue(TNode::iterator i)
  {
    if (disabled()) return nullptr;
    return mkProof(
        PfRule::AND_ELIM, {mkProof(d_parent)}, {mkRat(i - d_parent.begin())});
  }

  /** or false  -->  child is false */
  std::shared_ptr<ProofNode> orFalse(TNode::iterator i)
  {
    if (disabled()) return nullptr;
    return mkNot(mkProof(PfRule::NOT_OR_ELIM,
                         {mkProof(d_parent.notNode())},
                         {mkRat(i - d_parent.begin())}));
  }

  /** (not x) is true  -->  x is false (and vice versa) */
  std::shared_ptr<ProofNode> Not()
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkProof(d_parentAssignment ? Node(d_parent) : d_parent.notNode()));
  }

  /**
   * Propagate on ite with evaluate condition
   * (ite true t e)  -->  t
   * (not (ite true t e))  -->  (not t)
   * (ite false t e)  -->  e
   * (not (ite false t e))  -->  (not e)
   */
  std::shared_ptr<ProofNode> iteC(bool c)
  {
    if (disabled()) return nullptr;
    if (d_parentAssignment)
    {
      return mkResolution(mkProof(c ? PfRule::ITE_ELIM1 : PfRule::ITE_ELIM2,
                                  {mkProof(d_parent)}),
                          {c ? d_parent[0].notNode() : Node(d_parent[0])});
    }
    else
    {
      return mkResolution(
          mkProof(c ? PfRule::NOT_ITE_ELIM1 : PfRule::NOT_ITE_ELIM2,
                  {mkProof(d_parent.notNode())}),
          {c ? d_parent[0].notNode() : Node(d_parent[0])});
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
    if (disabled()) return nullptr;
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
    if (disabled()) return nullptr;
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

  /** (not (=> X Y))  -->  X */
  std::shared_ptr<ProofNode> impliesNegX()
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkProof(PfRule::NOT_IMPLIES_ELIM1, {mkProof(d_parent.notNode())}));
  }
  /** (not (=> X Y))  -->  (not Y) */
  std::shared_ptr<ProofNode> impliesNegY()
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

  /** All children are true  -->  and is true */
  std::shared_ptr<ProofNode> andAllTrue()
  {
    if (disabled()) return nullptr;
    std::vector<std::shared_ptr<ProofNode>> children;
    for (const auto& child : d_parent)
    {
      children.emplace_back(mkProof(child));
    }
    return mkProof(PfRule::AND_INTRO, children);
  }
  /** One child is false  -->  and is false */
  std::shared_ptr<ProofNode> andOneFalse()
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

  /** One child is true  -->  or is true */
  std::shared_ptr<ProofNode> orOneTrue()
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
  std::shared_ptr<ProofNode> orFalse()
  {
    if (disabled()) return nullptr;
    std::vector<Node> children(d_parent.begin(), d_parent.end());
    return mkResolution(mkProof(PfRule::CNF_OR_POS, {}, {d_parent}), children);
  }

  /** x is true  -->  (not x) is false (and vice versa) */
  std::shared_ptr<ProofNode> Not()
  {
    if (disabled()) return nullptr;
    return mkNot(
        mkProof(d_childAssignment ? d_parent.notNode() : Node(d_parent)));
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
      return mkResolution(
          mkProof(PfRule::NOT_EQUIV_ELIM2, {mkProof(d_parent.notNode())}),
          {d_child.notNode()});
    }
    else
    {
      return mkResolution(
          mkProof(PfRule::NOT_EQUIV_ELIM1, {mkProof(d_parent.notNode())}),
          {d_child});
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

  /** Evaluate (=> X Y) from X,Y */
  std::shared_ptr<ProofNode> impliesEval(bool premise, bool conclusion)
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
  std::shared_ptr<ProofNode> xorXFromY(bool negated)
  {
    return mkXorXFromY(negated, d_childAssignment, d_parent);
  }
  std::shared_ptr<ProofNode> xorYFromX(bool negated)
  {
    return mkXorYFromX(negated, d_childAssignment, d_parent);
  }
  std::shared_ptr<ProofNode> xorEval(bool x, bool y)
  {
    if (disabled()) return nullptr;
    if (x && y)
    {
      return mkResolution(mkProof(PfRule::CNF_XOR_POS2, {}, {d_parent}),
                          {d_parent[0].notNode(), d_parent[1].notNode()});
    }
    else if (x && !y)
    {
      return mkResolution(mkProof(PfRule::CNF_XOR_NEG1, {}, {d_parent}),
                          {d_parent[0].notNode(), d_parent[1]});
    }
    else if (!x && y)
    {
      return mkResolution(mkProof(PfRule::CNF_XOR_NEG2, {}, {d_parent}),
                          {d_parent[0], d_parent[1].notNode()});
    }
    else
    {
      Assert(!x && !y);
      return mkResolution(mkProof(PfRule::CNF_XOR_POS1, {}, {d_parent}),
                          {d_parent[0], d_parent[1]});
    }
  }
  };

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

#endif
