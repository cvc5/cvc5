/*********************                                                        */
/*! \file simple_bitblaster.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitblaster for simple BV solver.
 **
 **/
#include "theory/bv/bitblast/simple_bitblaster.h"

#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

BBSimple::BBSimple(TheoryState* s) : TBitblaster<Node>(), d_state(s) {}

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

bool BBSimple::hasBBAtom(TNode lit) const
{
  if (lit.getKind() == kind::NOT)
  {
    lit = lit[0];
  }
  return d_bbAtoms.find(lit) != d_bbAtoms.end();
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

bool BBSimple::isVariable(TNode node)
{
  return d_variables.find(node) != d_variables.end();
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
