/*********************                                                        */
/*! \file bv_solver_simple.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple bit-blast solver
 **
 ** Simple bit-blast solver that sends bitblast lemmas directly to MiniSat.
 **/

#include "theory/bv/bv_solver_simple.h"

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

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

BVSolverSimple::BVSolverSimple(TheoryState* s,
                               TheoryInferenceManager& inferMgr,
                               ProofNodeManager* pnm)
    : BVSolver(*s, inferMgr),
      d_bitblaster(new BBSimple(s)),
      d_epg(pnm ? new EagerProofGenerator(pnm, s->getUserContext(), "")
                : nullptr)
{
  if (pnm != nullptr)
  {
    d_bvProofChecker.registerTo(pnm->getChecker());
  }
}

void BVSolverSimple::addBBLemma(TNode fact)
{
  if (!d_bitblaster->hasBBAtom(fact))
  {
    d_bitblaster->bbAtom(fact);
  }
  NodeManager* nm = NodeManager::currentNM();

  Node atom_bb = d_bitblaster->getStoredBBAtom(fact);
  Node lemma = nm->mkNode(kind::EQUAL, fact, atom_bb);

  if (d_epg == nullptr)
  {
    d_inferManager.lemma(lemma);
  }
  else
  {
    TrustNode tlem = d_epg->mkTrustNode(lemma, PfRule::BV_BITBLAST, {}, {fact});
    d_inferManager.trustedLemma(tlem);
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

    if (d_epg == nullptr)
    {
      d_inferManager.lemma(lemma);
    }
    else
    {
      TrustNode tlem =
          d_epg->mkTrustNode(lemma, PfRule::BV_EAGER_ATOM, {}, {fact});
      d_inferManager.trustedLemma(tlem);
    }

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
