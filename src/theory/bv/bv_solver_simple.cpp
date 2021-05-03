/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Gereon Kremer, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple bit-blast solver that sends bitblast lemmas directly to MiniSat.
 */

#include "theory/bv/bv_solver_simple.h"

#include "expr/term_conversion_proof_generator.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5 {
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
      d_tcpg(pnm ? new TConvProofGenerator(
                 pnm,
                 nullptr,
                 /* ONCE to visit each term only once, post-order.  FIXPOINT
                  * could lead to infinite loops due to terms being rewritten
                  * to terms that contain themselves */
                 TConvPolicy::ONCE,
                 /* STATIC to get the same ProofNode for a shared subterm. */
                 TConvCachePolicy::STATIC,
                 "BVSolverSimple::TConvProofGenerator",
                 nullptr,
                 false)
                 : nullptr),
      d_bitblaster(new BBProof(s, pnm, d_tcpg.get()))
{
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

  if (d_tcpg == nullptr)
  {
    d_im.lemma(lemma, InferenceId::BV_SIMPLE_BITBLAST_LEMMA);
  }
  else
  {
    TrustNode tlem = TrustNode::mkTrustLemma(lemma, d_tcpg.get());
    d_im.trustedLemma(tlem, InferenceId::BV_SIMPLE_BITBLAST_LEMMA);
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

    if (d_tcpg == nullptr)
    {
      d_im.lemma(lemma, InferenceId::BV_SIMPLE_LEMMA);
    }
    else
    {
      TrustNode tlem = TrustNode::mkTrustLemma(lemma, d_tcpg.get());
      d_im.trustedLemma(tlem, InferenceId::BV_SIMPLE_LEMMA);
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

BVProofRuleChecker* BVSolverSimple::getProofChecker() { return &d_checker; }

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
