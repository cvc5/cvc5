/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof rule checker.
 */

#include "proof/proof_rule_checker.h"

#include "proof/proof_node.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

Node ProofRuleChecker::check(ProofRule id,
                             const std::vector<Node>& children,
                             const std::vector<Node>& args)
{
  // call instance-specific checkInternal method
  return checkInternal(id, children, args);
}

bool ProofRuleChecker::getUInt32(TNode n, uint32_t& i)
{
  // must be a non-negative integer constant that fits an unsigned int
  if (n.getKind() == Kind::CONST_INTEGER && n.getConst<Rational>().sgn() >= 0
      && n.getConst<Rational>().getNumerator().fitsUnsignedInt())
  {
    i = n.getConst<Rational>().getNumerator().toUnsignedInt();
    return true;
  }
  return false;
}

bool ProofRuleChecker::getBool(TNode n, bool& b)
{
  if (n.isConst() && n.getType().isBoolean())
  {
    b = n.getConst<bool>();
    return true;
  }
  return false;
}

bool ProofRuleChecker::getKind(TNode n, Kind& k)
{
  uint32_t i;
  if (!getUInt32(n, i))
  {
    return false;
  }
  k = static_cast<Kind>(i);
  return true;
}

Node ProofRuleChecker::mkKindNode(NodeManager* nm, Kind k)
{
  if (k == Kind::UNDEFINED_KIND)
  {
    // UNDEFINED_KIND is negative, hence return null to avoid cast
    return Node::null();
  }
  return nm->mkConstInt(Rational(static_cast<uint32_t>(k)));
}

NodeManager* ProofRuleChecker::nodeManager() const { return d_nm; }

}  // namespace cvc5::internal
