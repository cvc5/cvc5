/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for monomials.
 */

#include "theory/arith/nl/ext/arith_nl_compare_proof_gen.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/ext/monomial_check.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ArithNlCompareProofGenerator::ArithNlCompareProofGenerator(Env& env) : EnvObj(env), d_absConv(env) {}
ArithNlCompareProofGenerator::~ArithNlCompareProofGenerator() {}

std::shared_ptr<ProofNode> ArithNlCompareProofGenerator::getProofFor(Node fact)
{
  Assert (fact.getKind()==Kind::IMPLIES);
  std::vector<Node> exp;
  if (fact[0].getKind()==Kind::AND)
  {
    exp.insert(exp.end(), fact[0].begin(), fact[0].end());
  }
  else
  {
    exp.emplace_back(fact[0]);
  }
  Node conc = fact[1];
  CDProof cdp(d_env);
  cdp.addStep(conc, ProofRule::MACRO_ARITH_NL_COMPARISON, exp, {conc});
  cdp.addStep(fact, ProofRule::SCOPE, {conc}, exp);
  return cdp.getProofFor(fact);
}

std::string ArithNlCompareProofGenerator::identify() const { return "ArithNlCompareProofGenerator"; }

Node ArithNlCompareProofGenerator::mkLit(NodeManager* nm, Kind k, Node a, Node b, bool isAbsolute)
{
  if (isAbsolute)
  {
    a = nm->mkNode(Kind::ABS, a);
    b = nm->mkNode(Kind::ABS, b);
  }
  if (k==Kind::EQUAL)
  {
    return mkEquality(a, b);
  }
  return nm->mkNode(k, a, b);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

