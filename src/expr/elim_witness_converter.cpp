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
 * Implementation of witness elimination node conversion
 */

#include "expr/elim_witness_converter.h"

#include "expr/skolem_manager.h"

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
    Node q = nm->mkNode(Kind::FORALL, nchildren);
    Node k = skm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE,
                                   {q, n[0][0]});
    d_exists.push_back(q.notNode());
    return k;
  }
  return n;
}
const std::vector<Node>& ElimWitnessNodeConverter::getExistentials() const
{
  return d_exists;
}

}  // namespace cvc5::internal
