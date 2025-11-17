/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {
namespace bv {

NodeBitblaster::NodeBitblaster(Env& env) : TBitblaster<Node>(), EnvObj(env) {}

void NodeBitblaster::bbAtom(TNode node)
{
  node = node.getKind() == Kind::NOT ? node[0] : node;

  if (hasBBAtom(node))
  {
    return;
  }

  /* Note: We rewrite here since it's not guaranteed (yet) that facts sent
   * to theories are rewritten.
   */
  Node atom_bb = rewrite(applyAtomBBStrategy(rewrite(node)));
  storeBBAtom(node, atom_bb);
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
  if (lit.getKind() == Kind::NOT)
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
    bits.push_back(utils::mkBit(var, i));
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
  d_termBBStrategies[static_cast<uint32_t>(node.getKind())](node, bits, this);
  Assert(bits.size() == utils::getSize(node));
  storeBBTerm(node, bits);
}

Node NodeBitblaster::getStoredBBAtom(TNode node) const
{
  bool negated = false;
  if (node.getKind() == Kind::NOT)
  {
    node = node[0];
    negated = true;
  }

  Assert(hasBBAtom(node));
  Node atom_bb = d_bbAtoms.at(node);
  return negated ? atom_bb.negate() : atom_bb;
}

void NodeBitblaster::collectVariables(std::set<Node>& termSet) const
{
  Assert(options().bv.bitblastMode == options::BitblastMode::EAGER);
  for (const auto& var : d_variables)
  {
    termSet.insert(var);
  }
}

bool NodeBitblaster::isVariable(TNode node) const
{
  return d_variables.find(node) != d_variables.end();
}

Node NodeBitblaster::applyAtomBBStrategy(TNode node)
{
  Kind kind = node.getKind();
  if (kind == Kind::CONST_BOOLEAN || kind == Kind::BITVECTOR_BIT)
  {
    return node;
  }
  return d_atomBBStrategies[static_cast<uint32_t>(kind)](node, this);
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
