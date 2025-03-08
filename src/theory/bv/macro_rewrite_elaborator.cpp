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
 * Methods for elaborating MACRO_BV_* proof rewrites.
 */

#include "theory/bv/macro_rewrite_elaborator.h"

#include "expr/aci_norm.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

MacroRewriteElaborator::MacroRewriteElaborator(Env& env) : EnvObj(env) {}
MacroRewriteElaborator::~MacroRewriteElaborator() {}
bool MacroRewriteElaborator::ensureProofFor(CDProof* cdp,
                                            ProofRewriteRule id,
                                            const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("bv-rew-elab") << "ensureProofFor: " << id << " " << eq << std::endl;
  switch (id)
  {
    case ProofRewriteRule::MACRO_BV_OR_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_AND_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_XOR_SIMPLIFY:
      return ensureProofForSimplify(cdp, eq);
    default: break;
  }
  // TODO PR #11676
  return false;
}

bool MacroRewriteElaborator::ensureProofForSimplify(CDProof* cdp,
                                                    const Node& eq)
{
  // below, we group all of the constant children into one nested
  // child, prove the grouping by ACI_NORM, evaluate the constant
  // child, then prove the equality by another instance of ACI_NORM
  // if necessary.
  NodeManager* nm = nodeManager();
  Kind k = eq[0].getKind();
  std::vector<Node> consts;
  std::vector<Node> nconsts;
  for (const Node& cc : eq[0])
  {
    if (cc.isConst())
    {
      consts.push_back(cc);
    }
    else
    {
      nconsts.push_back(cc);
    }
  }
  if (consts.size() <= 1 || nconsts.empty())
  {
    Assert(false) << "BV simplify: no constant eval";
    return false;
  }
  std::vector<Node> transEq;
  Node cc = nm->mkNode(k, consts);
  nconsts.insert(nconsts.begin(), cc);
  Node eq0c = nm->mkNode(k, nconsts);
  Node equiv1 = eq[0].eqNode(eq0c);
  cdp->addStep(equiv1, ProofRule::ACI_NORM, {}, {equiv1});
  transEq.push_back(equiv1);
  Node ccr = evaluate(cc, {}, {});
  Node ceq = cc.eqNode(ccr);
  cdp->addTrustedStep(ceq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  std::vector<Node> premises;
  premises.push_back(ceq);
  Node equiv2 = proveCong(cdp, eq0c, premises);
  Assert(equiv2.getKind() == Kind::EQUAL);
  transEq.push_back(equiv2);
  if (equiv2[1] != eq[1])
  {
    // could be ACI_NORM or ABSORB, just send generic subgoal.
    Node equiv3 = equiv2[1].eqNode(eq[1]);
    cdp->addTrustedStep(
        equiv3, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(equiv3);
  }
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

Node MacroRewriteElaborator::proveCong(CDProof* cdp,
                                       const Node& n,
                                       const std::vector<Node>& premises)
{
  std::vector<Node> cpremises = premises;
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(n, cargs);
  cpremises.resize(n.getNumChildren());
  // add REFL if a premise is not provided
  for (size_t i = 0, npremises = cpremises.size(); i < npremises; i++)
  {
    if (cpremises[i].isNull())
    {
      Node refl = n[i].eqNode(n[i]);
      cdp->addStep(refl, ProofRule::REFL, {}, {n[i]});
      cpremises[i] = refl;
    }
  }
  Trace("brc-macro") << "- cong " << cr << " " << cpremises << " " << cargs
                     << std::endl;
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node eq = pc->checkDebug(cr, cpremises, cargs);
  Trace("brc-macro") << "...returns " << eq << std::endl;
  if (!eq.isNull())
  {
    cdp->addStep(eq, cr, cpremises, cargs);
  }
  return eq;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
