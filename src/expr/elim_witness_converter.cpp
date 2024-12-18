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

#include "proof/valid_witness_proof_generator.h"
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
    std::vector<Node> pats;
    Node k;
    if (n.getNumChildren() == 3)
    {
      // see if it has a proof specification marking, in which case we can
      // introduce a skolem and axiom in the proper way
      Assert(n[2].getKind() == Kind::INST_PATTERN_LIST);
      ProofRule r;
      std::vector<Node> args;
      if (ValidWitnessProofGenerator::getProofSpec(nm, n[2][0], r, args))
      {
        k = ValidWitnessProofGenerator::mkSkolem(nm, r, args);
        Node ax = ValidWitnessProofGenerator::mkAxiom(nm, k, r, args);
        Assert(!ax.isNull());
        if (!ax.isNull())
        {
          d_axioms.push_back(ax);
        }
      }
    }
    Assert(!k.isNull());
    return k;
  }
  return n;
}

const std::vector<Node>& ElimWitnessNodeConverter::getAxioms() const
{
  return d_axioms;
}

}  // namespace cvc5::internal
