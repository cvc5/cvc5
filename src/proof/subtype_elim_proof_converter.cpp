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

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

SubtypeElimConverterCallback::SubtypeElimConverterCallback(Env& env)
    : EnvObj(env)
{
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
  // Node resc = d_nconv.convert(res);
  //  see if proof rule still works
  Node resc = d_nconv.convert(res);
  Node newRes;
  // if either failed or succeeded outright
  if (tryWith(id, children, cargs, resc, newRes, cdp))
  {
    if (newRes.isNull())
    {
      Trace("pf-subtype-elim")
          << "Failed to convert subtyping " << id << std::endl;
      Trace("pf-subtype-elim") << "Premises: " << children << std::endl;
      Trace("pf-subtype-elim") << "Args: " << cargs << std::endl;
      AlwaysAssert(false) << "Failed to convert subtyping " << id;
    }
    return newRes;
  }
  Trace("pf-subtype-elim") << "Introduction of subtyping via rule " << id
                           << std::endl;
  Trace("pf-subtype-elim") << "Premises: " << children << std::endl;
  Trace("pf-subtype-elim") << "Args: " << cargs << std::endl;
  Trace("pf-subtype-elim") << "...gives " << newRes << std::endl;
  Trace("pf-subtype-elim") << "...wants " << resc << std::endl;
  bool success = false;
  switch (id)
  {
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    {
      success = true;
      Node lhs = resc[0];
      Node rhs = resc[1];
      for (size_t i = 0, nchild = lhs.getNumChildren(); i < nchild; i++)
      {
        Node eqOld = newRes[0][i].eqNode(newRes[1][i]);
        Node eqNew = lhs[i].eqNode(rhs[i]);
        // prove equality
        if (!prove(eqOld, eqNew, cdp))
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        newRes = resc;
      }
    }
    break;
    case ProofRule::ARITH_SUM_UB:
    {
      Assert(resc.getNumChildren() == 2);
    }
    break;
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
    {
      NodeManager * nm = NodeManager::currentNM();
      Node sc = resc[0][0];
      Node relOld = resc[0][1];
      Node relNew = nm->mkNode(resc[1].getKind(), resc[1][0][1], resc[1][1][1]);
      if (prove(relOld, relNew, cdp))
      {
        Node relNewMult = resc[1];
        Node rimpl = nm->mkNode(Kind::IMPLIES, sc, relNewMult);
        cdp->addStep(rimpl, id, {}, {args[0], relNew});
        cdp->addStep(relNewMult, ProofRule::MODUS_PONENS, {rimpl, sc}, {});
        cdp->addStep(resc, ProofRule::SCOPE, {relNewMult}, {sc, relOld});
      }
    }
    break;
    case ProofRule::MACRO_SR_EQ_INTRO:
    {
      // just use the more general rule MACRO_SR_PRED_INTRO, where the converted result can be used.
      cargs[0] = resc;
      if (tryWith(ProofRule::MACRO_SR_PRED_INTRO,
                  children,
                  cargs,
                  resc,
                  newRes,
                  cdp))
      {
        success = !newRes.isNull();
      }
    }
    break;
    case ProofRule::TRUST_THEORY_REWRITE: break;
    default: break;
  }
  if (success)
  {
    return newRes;
  }
  AlwaysAssert(false) << "Introduction of subtyping via rule " << id;
  return Node::null();
}

bool SubtypeElimConverterCallback::tryWith(ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           Node resc,
                                           Node& newRes,
                                           CDProof* cdp)
{
  newRes = d_pc->checkDebug(id, children, args);
  if (!newRes.isNull())
  {
    // check if the new result has subtyping
    if (resc == newRes)
    {
      cdp->addStep(newRes, id, children, args);
      return true;
    }
    return false;
  }
  return true;
}

bool SubtypeElimConverterCallback::prove(const Node& src, const Node& tgt, CDProof* cdp)
{
  Assert (src.getKind()==tgt.getKind());
  Assert (src.getNumChildren()==2);
  Assert (tgt.getNumChildren()==2);
  if (tgt==src)
  {
    return true;
  }
  if (tgt.getKind()==Kind::EQUAL && tgt[0]==tgt[1])
  {
    cdp->addStep(tgt, ProofRule::REFL, {}, {tgt[0]});
    return true;
  }
  Trace("pf-subtype-elim") << "Prove " << src << " => " << tgt << "?" << std::endl;
  // t=s becomes (to_real t)=(to_real s), or t=0 becomes (to_real t)=0.0
  Node conv[2];
  Node convEq[2];
  NodeManager* nm = NodeManager::currentNM();
  for (size_t j = 0; j < 2; j++)
  {
    conv[j] = nm->mkNode(Kind::TO_REAL, src[j]);
    if (conv[j] != tgt[j])
    {
      // if e.g. (to_real 0) = 0.0, prove by evaluate
      Node eq = j == 1 ? conv[j].eqNode(tgt[j])
                        : tgt[j].eqNode(conv[j]);
      Node peq = d_pc->checkDebug(ProofRule::EVALUATE, {}, {conv[j]});
      if (!CDProof::isSame(eq, peq))
      {
        return false;
      }
      convEq[j] = eq;
    }
  }
  if (tgt.getKind()==Kind::EQUAL)
  {
    Node nk = ProofRuleChecker::mkKindNode(Kind::TO_REAL);
    Node ceq = conv[0].eqNode(conv[1]);
    cdp->addStep(ceq, ProofRule::CONG, {src}, {nk});
    Trace("pf-subtype-elim") << "...via " << ceq << std::endl;
    if (ceq!=tgt)
    {
      std::vector<Node> tchildren;
      if (!convEq[0].isNull())
      {
        tchildren.push_back(convEq[0]);
      }
      tchildren.push_back(ceq);
      if (!convEq[1].isNull())
      {
        tchildren.push_back(convEq[1]);
      }
      cdp->addStep(tgt, ProofRule::TRANS, tchildren, {});
      Trace("pf-subtype-elim")
          << "...via trans " << tchildren << std::endl;
    }
  }
  else
  {
    Trace("pf-subtype-elim") << "prove via " << src << ", " << convEq[0] << ", " << convEq[1] << std::endl;
  }
  return true;
}

}  // namespace cvc5::internal
