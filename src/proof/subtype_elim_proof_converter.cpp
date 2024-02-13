/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proof nodes.
 */

#include "proof/subtype_elim_proof_converter.h"
#include "smt/env.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_checker.h"
#include "proof/proof.h"

namespace cvc5::internal {

SubtypeElimConverterCallback::SubtypeElimConverterCallback(Env& env) : EnvObj(env) {
  d_pc = d_env.getProofNodeManager()->getChecker();
}

Node SubtypeElimConverterCallback::convert(Node res,
                      ProofRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      CDProof* cdp)
{
  std::vector<Node> cargs;
  for (const Node& a : args)
  {
    cargs.push_back(d_nconv.convert(a));
  }
  // see if proof rule still works
  Node newRes = d_pc->checkDebug(id, children, cargs);
  if (newRes.isNull())
  {
    AlwaysAssert(false) << "Failed to convert subtyping " << id;
    Trace("ajr-temp") << "Failed to convert subtyping " << id << std::endl;
    Trace("ajr-temp") << "Premises: " << children << std::endl;
    Trace("ajr-temp") << "Args: " << cargs << std::endl;
    // FAILED
    return Node::null();
  }
  Node newResc = d_nconv.convert(newRes);
  if (newResc==newRes)
  {
    // rule worked
    cdp->addStep(newRes, id, children, cargs);
    return newRes;
  }
  Trace("ajr-temp") << "Introduction of subtyping via rule " << id << std::endl;
  Trace("ajr-temp") << "Premises: " << children << std::endl;
  Trace("ajr-temp") << "Args: " << cargs << std::endl;
  Trace("ajr-temp") << "...gives " << newRes << std::endl;
  Trace("ajr-temp") << "...wants " << newResc << std::endl;
  bool success = false;
  switch (id)
  {
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    {
      success = true;
      Node lhs = newResc[0];
      Node rhs = newResc[1];
      for (size_t i=0, nchild = lhs.getNumChildren(); i<nchild; i++)
      {
        Node eqOld = newRes[0][i].eqNode(newRes[1][i]);
        Node eqNew = lhs[i].eqNode(rhs[i]);
        if (eqOld==eqNew)
        {
          continue;
        }
        if (lhs[i]==rhs[i])
        {
          cdp->addStep(eqNew, ProofRule::REFL, {}, {lhs[i]});
          continue;
        }
        success = false;
        break;
      }
    }
      break;
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
      break;
    case ProofRule::MACRO_ARITH_SCALE_SUM_UB:
      break;
    case ProofRule::MACRO_SR_EQ_INTRO:
    case ProofRule::SKOLEM_INTRO:
      break;
    case ProofRule::TRUST_THEORY_REWRITE:
      break;
    default:
      break;
  }
  if (success)
  {
    return newResc;
  }
  AlwaysAssert(false) << "Introduction of subtyping via rule " << id;
  return Node::null();
}

}  // namespace cvc5::internal

