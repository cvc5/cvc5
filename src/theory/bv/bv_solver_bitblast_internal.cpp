/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blast solver that sends bit-blast lemmas directly to the internal
 * MiniSat.
 */

#include "theory/bv/bv_solver_bitblast_internal.h"

#include "options/bv_options.h"
#include "proof/conv_proof_generator.h"
#include "theory/bv/bitblast/bitblast_proof_generator.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

namespace {

bool isBVAtom(TNode n)
{
  return (n.getKind() == Kind::EQUAL && n[0].getType().isBitVector())
         || n.getKind() == Kind::BITVECTOR_ULT
         || n.getKind() == Kind::BITVECTOR_ULE
         || n.getKind() == Kind::BITVECTOR_SLT
         || n.getKind() == Kind::BITVECTOR_SLE;
}

/* Traverse Boolean nodes and collect BV atoms. */
void collectBVAtoms(TNode n, std::unordered_set<Node>& atoms)
{
  std::vector<TNode> visit;
  std::unordered_set<TNode> visited;

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

BVSolverBitblastInternal::BVSolverBitblastInternal(
    Env& env, TheoryState& state, TheoryInferenceManager& inferMgr)
    : BVSolver(env, state, inferMgr),
      d_bitblaster(new BBProof(env, false)),
      d_epg(new EagerProofGenerator(d_env))
{
}

void BVSolverBitblastInternal::addBBLemma(TNode fact)
{
  if (!d_bitblaster->hasBBAtom(fact))
  {
    d_bitblaster->bbAtom(fact);
  }
  NodeManager* nm = nodeManager();

  Node atom_bb = d_bitblaster->getBBAtom(fact);
  Node lemma = nm->mkNode(Kind::EQUAL, fact, atom_bb);

  if (!d_env.isTheoryProofProducing())
  {
    d_im.lemma(lemma, InferenceId::BV_BITBLAST_INTERNAL_BITBLAST_LEMMA);
  }
  else
  {
    TrustNode tlem =
        TrustNode::mkTrustLemma(lemma, d_bitblaster->getProofGenerator());
    d_im.trustedLemma(tlem, InferenceId::BV_BITBLAST_INTERNAL_BITBLAST_LEMMA);
  }
}

bool BVSolverBitblastInternal::needsEqualityEngine(EeSetupInfo& esi)
{
  // Disable equality engine if --bitblast=eager is enabled.
  return options().bv.bitblastMode != options::BitblastMode::EAGER;
}

bool BVSolverBitblastInternal::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (fact.getKind() == Kind::NOT)
  {
    fact = fact[0];
  }

  if (isBVAtom(fact))
  {
    addBBLemma(fact);
  }
  else if (fact.getKind() == Kind::BITVECTOR_EAGER_ATOM)
  {
    TNode n = fact[0];

    NodeManager* nm = nodeManager();
    Node lemma = nm->mkNode(Kind::EQUAL, fact, n);

    if (!d_env.isTheoryProofProducing())
    {
      d_im.lemma(lemma, InferenceId::BV_BITBLAST_INTERNAL_EAGER_LEMMA);
    }
    else
    {
      TrustNode tlem =
          d_epg->mkTrustNode(lemma, ProofRule::BV_EAGER_ATOM, {}, {fact});
      d_im.trustedLemma(tlem, InferenceId::BV_BITBLAST_INTERNAL_EAGER_LEMMA);
    }

    std::unordered_set<Node> bv_atoms;
    collectBVAtoms(n, bv_atoms);
    for (const Node& nn : bv_atoms)
    {
      addBBLemma(nn);
    }
  }

  // Disable the equality engine in --bitblast=eager mode. Otherwise return
  // false to enable equality engine reasoning in Theory.
  return options().bv.bitblastMode == options::BitblastMode::EAGER;
}

TrustNode BVSolverBitblastInternal::explain(TNode n)
{
  Trace("bv-bitblast-internal") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

bool BVSolverBitblastInternal::collectModelValues(TheoryModel* m,
                                                  const std::set<Node>& termSet)
{
  for (const auto& var : termSet)
  {
    if (!d_bitblaster->isVariable(var)) continue;

    Node const_value = getValue(var, true);
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

Node BVSolverBitblastInternal::getValue(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }

  NodeManager* nm = node.getNodeManager();
  if (!d_bitblaster->hasBBTerm(node))
  {
    return initialize ? utils::mkConst(nm, utils::getSize(node), 0u) : Node();
  }

  std::vector<Node> bits;
  d_bitblaster->getBBTerm(node, bits);
  Integer value(0);
  const Integer one(1), zero(0);
  for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)
  {
    Integer bit;
    if (bool satValue; d_state.hasSatValue(bits[j], satValue))
    {
      bit = satValue ? one : zero;
    }
    else
    {
      if (!initialize) return Node();
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(nm, bits.size(), value);
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
