/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitblaster used to bitblast to Boolean Nodes.
 */
#include "theory/bv/bitblast/node_bitblaster.h"

#include "options/bv_options.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

NodeBitblaster::NodeBitblaster(Env& env, TheoryState* s)
    : TBitblaster<Node>(), EnvObj(env), d_state(s)
{
}

void NodeBitblaster::bbAtom(TNode node)
{
  node = node.getKind() == kind::NOT ? node[0] : node;

  if (hasBBAtom(node))
  {
    return;
  }

  /* Note: We rewrite here since it's not guaranteed (yet) that facts sent
   * to theories are rewritten.
   */
  Node normalized = rewrite(node);
  Node atom_bb =
      normalized.getKind() != kind::CONST_BOOLEAN
              && normalized.getKind() != kind::BITVECTOR_BITOF
          ? d_atomBBStrategies[normalized.getKind()](normalized, this)
          : normalized;

  storeBBAtom(node, rewrite(atom_bb));
}

void NodeBitblaster::storeBBAtom(TNode atom, Node atom_bb)
{
  d_bbAtoms.emplace(atom, atom_bb);
}

void NodeBitblaster::storeBBTerm(TNode node, const Bits& bits)
{
  d_termCache.emplace(node, bits);
}

bool NodeBitblaster::hasBBAtom(TNode lit) const
{
  if (lit.getKind() == kind::NOT)
  {
    lit = lit[0];
  }
  return d_bbAtoms.find(lit) != d_bbAtoms.end();
}

void NodeBitblaster::makeVariable(TNode var, Bits& bits)
{
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i)
  {
    bits.push_back(utils::mkBitOf(var, i));
  }
  d_variables.insert(var);
}

Node NodeBitblaster::getBBAtom(TNode node) const { return node; }

void NodeBitblaster::bbTerm(TNode node, Bits& bits)
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

Node NodeBitblaster::getStoredBBAtom(TNode node)
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

Node NodeBitblaster::getModelFromSatSolver(TNode a, bool fullModel)
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
    if (d_state->hasSatValue(bits[i], assignment))
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

void NodeBitblaster::computeRelevantTerms(std::set<Node>& termSet)
{
  Assert(options().bv.bitblastMode == options::BitblastMode::EAGER);
  for (const auto& var : d_variables)
  {
    termSet.insert(var);
  }
}

bool NodeBitblaster::collectModelValues(TheoryModel* m,
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

bool NodeBitblaster::isVariable(TNode node)
{
  return d_variables.find(node) != d_variables.end();
}

Node NodeBitblaster::applyAtomBBStrategy(TNode node)
{
  Assert(node.getKind() != kind::CONST_BOOLEAN);
  Assert(node.getKind() != kind::BITVECTOR_BITOF);
  return d_atomBBStrategies[node.getKind()](node, this);
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
