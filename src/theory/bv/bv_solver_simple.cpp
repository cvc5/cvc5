/*********************                                                        */
/*! \file bv_solver_simple.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple bit-blast solver
 **
 ** Simple bit-blast solver that sends bitblast lemmas directly to MiniSat.
 **/

#include "theory/bv/bv_solver_simple.h"

#include "theory/bv/bitblast/lazy_bitblaster.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BBSimple : public TBitblaster<Node>
{
  using Bits = std::vector<Node>;

 public:
  BBSimple(TheoryState& state);
  ~BBSimple() = default;

  void bbTerm(TNode node, Bits& bits) override;
  void bbAtom(TNode node) override;
  Node getBBAtom(TNode atom) const override;
  void storeBBAtom(TNode atom, Node atom_bb) override;
  void storeBBTerm(TNode node, const Bits& bits) override;
  bool hasBBAtom(TNode atom) const override;
  Node getStoredBBAtom(TNode node);

  void makeVariable(TNode var, Bits& bits) override;

  bool collectModelValues(TheoryModel* m, const std::set<Node>& relevantTerms);

  prop::SatSolver* getSatSolver() override { return nullptr; }

 private:
  Node getModelFromSatSolver(TNode a, bool fullModel) override;

  TNodeSet d_variables;
  std::unordered_map<Node, Node, NodeHashFunction> d_bbAtoms;
  TheoryState& d_state;
};

BBSimple::BBSimple(TheoryState& s) : TBitblaster<Node>(), d_state(s) {}

void BBSimple::bbAtom(TNode node)
{
  node = node.getKind() == kind::NOT ? node[0] : node;

  if (hasBBAtom(node))
  {
    return;
  }

  Node normalized = Rewriter::rewrite(node);
  Node atom_bb =
      normalized.getKind() != kind::CONST_BOOLEAN
              && normalized.getKind() != kind::BITVECTOR_BITOF
          ? d_atomBBStrategies[normalized.getKind()](normalized, this)
          : normalized;

  storeBBAtom(node, atom_bb);
}

void BBSimple::storeBBAtom(TNode atom, Node atom_bb)
{
  d_bbAtoms.emplace(atom, atom_bb);
}

void BBSimple::storeBBTerm(TNode node, const Bits& bits)
{
  d_termCache.emplace(node, bits);
}

bool BBSimple::hasBBAtom(TNode atom) const
{
  return d_bbAtoms.find(atom) != d_bbAtoms.end();
}

void BBSimple::makeVariable(TNode var, Bits& bits)
{
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i)
  {
    bits.push_back(utils::mkBitOf(var, i));
  }
  d_variables.insert(var);
}

// cnf conversion ensures the atom represents itself
Node BBSimple::getBBAtom(TNode node) const { return node; }

void BBSimple::bbTerm(TNode node, Bits& bits)
{
  Assert(node.getType().isBitVector());
  if (hasBBTerm(node))
  {
    getBBTerm(node, bits);
    return;
  }
  d_termBBStrategies[node.getKind()](node, bits, this);
  Assert(bits.size() == utils::getSize(node));
  storeBBTerm(node, bits);
}

Node BBSimple::getStoredBBAtom(TNode node)
{
  bool negated = false;
  if (node.getKind() == kind::NOT)
  {
    node = node[0];
    negated = true;
  }

  Assert(hasBBAtom(node));
  Node atom_bb = d_bbAtoms.at(node);
  return negated ? atom_bb.negate() : atom_bb;
}

Node BBSimple::getModelFromSatSolver(TNode a, bool fullModel)
{
  if (!hasBBTerm(a))
  {
    return utils::mkConst(utils::getSize(a), 0u);
  }

  bool assignment;
  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  Integer one(1), zero(0);
  for (int i = bits.size() - 1; i >= 0; --i)
  {
    Integer bit;
    if (d_state.hasSatValue(bits[i], assignment))
    {
      bit = assignment ? one : zero;
    }
    else
    {
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(bits.size(), value);
}

bool BBSimple::collectModelValues(TheoryModel* m,
                                  const std::set<Node>& relevantTerms)
{
  for (const auto& var : relevantTerms)
  {
    if (d_variables.find(var) == d_variables.end()) continue;

    Node const_value = getModelFromSatSolver(var, true);
    Assert(const_value.isNull() || const_value.isConst());
    if (!const_value.isNull())
    {
      if (!m->assertEquality(var, const_value, true))
      {
        return false;
      }
    }
  }
  return true;
}

/* -------------------------------------------------------------------------- */

namespace {

bool isBVAtom(TNode n)
{
  return (n.getKind() == kind::EQUAL && n[0].getType().isBitVector())
         || n.getKind() == kind::BITVECTOR_ULT
         || n.getKind() == kind::BITVECTOR_ULE
         || n.getKind() == kind::BITVECTOR_SLT
         || n.getKind() == kind::BITVECTOR_SLE;
}

/* Traverse Boolean nodes and collect BV atoms. */
void collectBVAtoms(TNode n, std::unordered_set<Node, NodeHashFunction>& atoms)
{
  std::vector<TNode> visit;
  std::unordered_set<TNode, TNodeHashFunction> visited;

  visit.push_back(n);

  do
  {
    TNode cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) != visited.end() || !cur.getType().isBoolean())
      continue;

    visited.insert(cur);
    if (isBVAtom(cur))
    {
      atoms.insert(cur);
      continue;
    }

    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
}

}  // namespace

BVSolverSimple::BVSolverSimple(TheoryState& s, TheoryInferenceManager& inferMgr)
    : BVSolver(s, inferMgr), d_bitblaster(new BBSimple(s)), d_lemmasCache()
{
}

void BVSolverSimple::addBBLemma(TNode fact)
{
  if (!d_bitblaster->hasBBAtom(fact))
  {
    d_bitblaster->bbAtom(fact);
  }
  if (d_lemmasCache.find(fact) == d_lemmasCache.end())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node atom_bb = Rewriter::rewrite(d_bitblaster->getStoredBBAtom(fact));
    Node lemma = nm->mkNode(kind::EQUAL, fact, atom_bb);
    d_inferManager.lemma(lemma);
  }
}

bool BVSolverSimple::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (fact.getKind() == kind::NOT)
  {
    fact = fact[0];
  }

  if (isBVAtom(fact))
  {
    addBBLemma(fact);
  }
  else if (fact.getKind() == kind::BITVECTOR_EAGER_ATOM)
  {
    TNode n = fact[0];

    NodeManager* nm = NodeManager::currentNM();
    Node lemma = nm->mkNode(kind::EQUAL, fact, n);
    d_inferManager.lemma(lemma);

    std::unordered_set<Node, NodeHashFunction> bv_atoms;
    collectBVAtoms(n, bv_atoms);
    for (const Node& nn : bv_atoms)
    {
      addBBLemma(nn);
    }
  }

  return true;
}

bool BVSolverSimple::collectModelValues(TheoryModel* m,
                                        const std::set<Node>& termSet)
{
  return d_bitblaster->collectModelValues(m, termSet);
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
