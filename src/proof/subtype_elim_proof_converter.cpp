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
 * A utility for converting proof nodes.
 */

#include "proof/subtype_elim_proof_converter.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

SubtypeElimConverterCallback::SubtypeElimConverterCallback(Env& env)
    : EnvObj(env), d_nconv(nodeManager())
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
  // get the converted form of the conclusion, which we must prove.
  Node resc = d_nconv.convert(res);
  // in very rare cases a direct child may already be the proof we want
  if (std::find(children.begin(), children.end(), resc) != children.end())
  {
    return resc;
  }
  Node newRes;
  // check if succeeds with no changes
  if (tryWith(id, children, cargs, resc, newRes, cdp))
  {
    Assert(newRes == resc);
    return resc;
  }
  else if (newRes.isNull())
  {
    // This case means we have nothing to work with. This should likely never
    // happen.
    Trace("pf-subtype-elim")
        << "Failed to convert subtyping " << id << std::endl;
    Trace("pf-subtype-elim") << "Premises: " << children << std::endl;
    Trace("pf-subtype-elim") << "Args: " << cargs << std::endl;
    return newRes;
  }
  // otherwise, newRes is what is proven from the rule without changes,
  // and resc is what we need to prove.
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
      std::vector<Node> newChildren;
      for (size_t i = 0, nchild = lhs.getNumChildren(); i < nchild; i++)
      {
        // eqOld is what was proven with the converted i-th child
        Node eqOld = newRes[0][i].eqNode(newRes[1][i]);
        // eqNew is what is necessary to prove
        Node eqNew = lhs[i].eqNode(rhs[i]);
        // eqOld and eqNew should essentially vary only in their types, e.g.
        // (= t s) vs. (= (to_real t) (to_real s)),
        // (= t 0) vs. (= (to_real t) 0.0), etc. We call prove to prove the
        // updated equality.
        if (!prove(eqOld, eqNew, cdp))
        {
          success = false;
          break;
        }
        newChildren.push_back(eqNew);
      }
      // proof with the original rule and updated children should now work
      if (success)
      {
        success = tryWith(id, newChildren, cargs, resc, newRes, cdp);
      }
    }
    break;
    case ProofRule::ARITH_SUM_UB:
    {
      success = true;
      NodeManager* nm = nodeManager();
      Assert(resc.getNumChildren() == 2);
      Assert(resc[0].getNumChildren() == children.size());
      Assert(resc[1].getNumChildren() == children.size());
      std::vector<Node> newChildren;
      // reprove what is necessary for the sum for each child
      for (size_t i = 0, nchild = children.size(); i < nchild; i++)
      {
        Node newRel = nm->mkNode(children[i].getKind(), resc[0][i], resc[1][i]);
        if (!prove(children[i], newRel, cdp))
        {
          success = false;
          break;
        }
        newChildren.push_back(newRel);
      }
      // proof with the original rule and updated children should now work
      if (success)
      {
        success = tryWith(
            ProofRule::ARITH_SUM_UB, newChildren, {}, resc, newRes, cdp);
      }
    }
    break;
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
    {
      // This handles the case where we multiply an integer relation by
      // a rational. We tranform the proof as follows:
      //
      //            ----- ASSUME
      //            t~s
      // --- ASSUME ----- prove, using method below
      // c>0        t'~s'
      // --------------- AND_INTRO ------------------------------ ARITH_MULT_X
      // (and c>0 t'~s')           (=> (and c>0 t'~s') (c*t'~c*s'))
      // ----------------------------------------------------- MODUS_PONENS
      // (c*t'~c*s')
      // ----------------------- SCOPE {c>0, t~s}
      // (=> (and c>0 t~s) (c*t'~c*s'))
      //
      // there t'~s' is a predicate over reals and t~s is a mixed integer
      // predicate.
      NodeManager* nm = nodeManager();
      Node sc = resc[0][0];
      Node relOld = resc[0][1];
      Node relNew = nm->mkNode(relOld.getKind(), resc[1][0][1], resc[1][1][1]);
      if (prove(relOld, relNew, cdp))
      {
        Node relNewMult = resc[1];
        Node antec = nm->mkNode(Kind::AND, sc, relNew);
        Node rimpl = nm->mkNode(Kind::IMPLIES, antec, relNewMult);
        cdp->addStep(rimpl, id, {}, {args[0], relNew});
        cdp->addStep(antec, ProofRule::AND_INTRO, {sc, relNew}, {});
        cdp->addStep(relNewMult, ProofRule::MODUS_PONENS, {antec, rimpl}, {});
        cdp->addStep(resc, ProofRule::SCOPE, {relNewMult}, {sc, relOld});
        success = true;
      }
    }
    break;
    case ProofRule::MACRO_SR_EQ_INTRO:
    {
      // Just use the more general rule MACRO_SR_PRED_INTRO, where the converted
      // result can be used. This is used to handle the case where
      // MACRO_SR_EQ_INTRO was used during solving.
      cargs[0] = resc;
      success = tryWith(
          ProofRule::MACRO_SR_PRED_INTRO, children, cargs, resc, newRes, cdp);
    }
    break;
    default: break;
  }
  if (!success)
  {
    // if we did not succeed, just add a trust step
    Trace("pf-subtype-elim-warn")
        << "WARNING: Introduction of subtyping via rule " << id;
    cdp->addTrustedStep(resc, TrustId::SUBTYPE_ELIMINATION, children, {});
  }
  return resc;
}

bool SubtypeElimConverterCallback::tryWith(ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           Node expected,
                                           Node& newRes,
                                           CDProof* cdp)
{
  newRes = d_pc->checkDebug(id, children, args);
  if (!newRes.isNull())
  {
    // check if the new result matches the result
    if (expected == newRes)
    {
      cdp->addStep(newRes, id, children, args);
      return true;
    }
  }
  return false;
}

bool SubtypeElimConverterCallback::prove(const Node& src,
                                         const Node& tgt,
                                         CDProof* cdp)
{
  Assert(src.getKind() == tgt.getKind());
  Assert(src.getNumChildren() == 2);
  Assert(tgt.getNumChildren() == 2);
  if (tgt == src)
  {
    return true;
  }
  if (tgt.getKind() == Kind::EQUAL && tgt[0] == tgt[1])
  {
    cdp->addStep(tgt, ProofRule::REFL, {}, {tgt[0]});
    return true;
  }
  Trace("pf-subtype-elim") << "Prove " << src << " => " << tgt << "?"
                           << std::endl;
  // t=s becomes (to_real t)=(to_real s), or t=0 becomes (to_real t)=0.0
  Node conv[2];
  Node convEq[2];
  NodeManager* nm = nodeManager();
  for (size_t j = 0; j < 2; j++)
  {
    conv[j] = nm->mkNode(Kind::TO_REAL, src[j]);
    convEq[j] = conv[j].eqNode(tgt[j]);
    if (conv[j] != tgt[j])
    {
      // if e.g. (to_real 0) = 0.0, prove by evaluate
      Node peq = d_pc->checkDebug(ProofRule::EVALUATE, {}, {conv[j]});
      if (peq != convEq[j])
      {
        return false;
      }
      cdp->addStep(peq, ProofRule::EVALUATE, {}, {conv[j]});
    }
    else
    {
      cdp->addStep(convEq[j], ProofRule::REFL, {}, {conv[j]});
    }
  }
  Node csrc = nm->mkNode(src.getKind(), conv[0], conv[1]);
  if (tgt.getKind() == Kind::EQUAL)
  {
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(csrc[0], cargs);
    cdp->addStep(csrc, cr, {src}, cargs);
    Trace("pf-subtype-elim") << "...via " << csrc << std::endl;
    if (csrc != tgt)
    {
      std::vector<Node> tchildren;
      if (convEq[0][0] != convEq[0][1])
      {
        // flip, proven by auto-sym.
        tchildren.push_back(convEq[0][1].eqNode(convEq[0][0]));
      }
      tchildren.push_back(csrc);
      if (convEq[1][0] != convEq[1][1])
      {
        tchildren.push_back(convEq[1]);
      }
      cdp->addStep(tgt, ProofRule::TRANS, tchildren, {});
      Trace("pf-subtype-elim") << "...via trans " << tchildren << std::endl;
      //                       ...
      // -------------- EVAL   ---
      // conv[0]=tgt[0]        src
      // -------------- SYMM   ----CONG{TO_REAL} -------------- EVAL
      // tgt[0]=conv[0]        conv              conv[1]=tgt[1]
      // ------------------------------------------------------ TRANS
      // tgt
      //
      // where conv is (to_real src[0]) = (to_real src[1]).
    }
  }
  else
  {
    Trace("pf-subtype-elim") << "prove via " << src << ", " << convEq[0] << ", "
                             << convEq[1] << std::endl;
    Node rewriteEq = src.eqNode(csrc);
    Node fullEq = src.eqNode(tgt);
    // we use a trust id here.
    cdp->addTrustedStep(
        rewriteEq, TrustId::ARITH_PRED_CAST_TYPE, {}, {rewriteEq});
    if (csrc != tgt)
    {
      Node congEq = csrc.eqNode(tgt);
      std::vector<Node> cargs;
      ProofRule cr = expr::getCongRule(csrc, cargs);
      cdp->addStep(congEq, cr, {convEq[0], convEq[1]}, cargs);
      cdp->addStep(fullEq, ProofRule::TRANS, {rewriteEq, congEq}, {});
    }
    cdp->addStep(tgt, ProofRule::EQ_RESOLVE, {src, fullEq}, {});
    //                                  -------------- -------------- EVAL(x2)
    //                                  conv[0]=tgt[0] conv[1]=tgt[1]
    //       ---------- AP_CAST_TYPE    ----------------------------- CONG{~}
    // ...   src = conv                 conv = tgt
    // ---   ------------------------------------------------ TRANS
    // src   src = tgt
    // ------------------------------------------------------ EQ_RESOLVE
    // tgt
    //
    // where conv is (to_real src[0]) = (to_real src[1]).
    // Note that we assume a theory rewrite step for proving e.g.
    // (< t s) = (< (to_real t) (to_real s)).
  }
  return true;
}

}  // namespace cvc5::internal
