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
#include "expr/attribute.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ArithNlCompareProofGenerator::ArithNlCompareProofGenerator(Env& env) : EnvObj(env) {}
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
  Trace("arith-nl-compare") << "Comparsion prove: " << exp << " => " << conc << std::endl;
  // get the expected form of the literals
  CDProof cdp(d_env);
  std::vector<Node> expc;
  for (const Node& e : exp)
  {
    Node ec = getCompareLit(e);
    if (ec.isNull())
    {
      expc.emplace_back(e);
      continue;
    }
    expc.emplace_back(ec);
    if (e!=ec)
    {
      Node eeq = e.eqNode(ec);
      cdp.addTrustedStep(eeq, TrustId::ARITH_NL_COMPARE_LIT_TRANSFORM, {}, {});
      cdp.addStep(ec, ProofRule::EQ_RESOLVE, {e, eeq}, {});
    }
  }
  Node concc = getCompareLit(conc);
  Assert (!concc.isNull());  
  Trace("arith-nl-compare") << "...processed prove: " << expc << " => " << concc << std::endl;
  cdp.addStep(concc, ProofRule::MACRO_ARITH_NL_COMPARISON, expc, {concc});
  if (conc!=concc)
  {
    Node ceq = concc.eqNode(conc);
    cdp.addTrustedStep(ceq, TrustId::ARITH_NL_COMPARE_LIT_TRANSFORM, {}, {});
    cdp.addStep(conc, ProofRule::EQ_RESOLVE, {concc, ceq}, {});
  }
  cdp.addStep(fact, ProofRule::SCOPE, {conc}, exp);
  AlwaysAssert(false);
  return cdp.getProofFor(fact);
}

std::string ArithNlCompareProofGenerator::identify() const { return "ArithNlCompareProofGenerator"; }

Node ArithNlCompareProofGenerator::mkLit(NodeManager* nm, Kind k, const Node& a, const Node& b, bool isAbsolute)
{
  Node au = a;
  Node bu = b;
  if (isAbsolute)
  {
    au = nm->mkNode(Kind::ABS, au);
    bu = nm->mkNode(Kind::ABS, bu);
  }
  if (k==Kind::EQUAL)
  {
    return mkEquality(au, bu);
  }
  return nm->mkNode(k, au, bu);
}

struct ArithNlCompareLitAttributeId
{
};
using ArithNlCompareLitAttribute = expr::Attribute<ArithNlCompareLitAttributeId, Node>;

void ArithNlCompareProofGenerator::setCompareLit(NodeManager* nm, Node olit, Kind k, const Node& a, const Node& b, bool isAbsolute)
{
  Node lit = mkLit(nm, k, a, b, isAbsolute);
  ArithNlCompareLitAttribute ancla;
  olit.setAttribute(ancla, lit);
}

Node ArithNlCompareProofGenerator::getCompareLit(const Node& olit)
{
  ArithNlCompareLitAttribute ancla;
  return olit.getAttribute(ancla);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

