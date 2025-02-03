/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of witness elimination node conversion
 */

#include "expr/elim_witness_converter.h"

#include "expr/skolem_manager.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "util/rational.h"

namespace cvc5::internal {

ElimWitnessNodeConverter::ElimWitnessNodeConverter(Env& env)
    : EnvObj(env), NodeConverter(nodeManager())
{
}

Node ElimWitnessNodeConverter::postConvert(Node n)
{
  if (n.getKind() == Kind::WITNESS)
  {
    Trace("elim-witness") << "Eliminate " << n << std::endl;
    NodeManager* nm = nodeManager();
    SkolemManager* skm = nm->getSkolemManager();
    std::vector<Node> nchildren(n.begin(), n.end());
    nchildren[1] = nchildren[1].notNode();
    // must mark that the quantified formula cannot be eliminated by rewriting,
    // so that the form of the quantified formula is preserved for the
    // introduction below.
    Node psan =
        theory::quantifiers::QuantAttributes::mkAttrPreserveStructure(nm);
    Node ipl = nm->mkNode(Kind::INST_PATTERN_LIST, psan);
    nchildren.push_back(ipl);
    // make the quantified formula
    Node q = nm->mkNode(Kind::FORALL, nchildren);
    Node qn = getNormalFormFor(q);
    // should still be a FORALL due to above
    Assert(qn.getKind() == Kind::FORALL);
    Node k = skm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE,
                                   {qn, nm->mkConstInt(Rational(0))});
    // save the non-normalized version, which makes it easier to e.g.
    // track proofs
    d_exists.push_back(q.notNode());
    return k;
  }
  return n;
}

Node ElimWitnessNodeConverter::getNormalFormFor(const Node& q) { return q; }

const std::vector<Node>& ElimWitnessNodeConverter::getExistentials() const
{
  return d_exists;
}

}  // namespace cvc5::internal
