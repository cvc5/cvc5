/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proof nodes.
 */

#include "proof/subtype_elim_proof_converter.h"

#include "expr/node_algorithm.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/arith/arith_utilities.h"
#include "util/rational.h"

namespace cvc5::internal {

SubtypeElimConverterCallback::SubtypeElimConverterCallback(Env& env)
    : EnvObj(env), d_nconv(nodeManager())
{
  d_pc = d_env.getProofNodeManager()->getChecker();
}

bool SubtypeElimConverterCallback::shouldConvert(std::shared_ptr<ProofNode> pn)
{
  // needs to convert if an argument or the result has mixed arithmetic, which
  // is true if the node converter modifies the term.
  const std::vector<Node>& args = pn->getArguments();
  for (const Node& a : args)
  {
    if (d_nconv.convert(a) != a)
    {
      return true;
    }
  }
  Node res = pn->getResult();
  return d_nconv.convert(res) != res;
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
  // trivial case: use refl. This handles all cases where e.g. rewriting
  // introduced mixed arithmetic. This happens commonly so we shortcut as
  // an optimization here.
  if (resc.getKind() == Kind::EQUAL && resc[0] == resc[1])
  {
    cdp->addStep(resc, ProofRule::REFL, {}, {resc[0]});
    return resc;
  }
  // in very rare cases a direct child may already be the proof we want
  if (std::find(children.begin(), children.end(), resc) != children.end())
  {
    return resc;
  }
  NodeManager* nm = nodeManager();
  // cases where arguments may need additional fixing before trying
  // proof rule
  switch (id)
  {
    case ProofRule::ARITH_MULT_SIGN:
    {
      Trace("pf-subtype-elim")
          << "preconvert arith mult sign " << cargs << std::endl;
      // For example, if x:Real, y:Int, this rule with the arguments
      // (and (> x 0.0) (> y 0)), (* x y) proves
      // (=> (and (> x 0.0) (> y 0)) (> (* x y) 0.0)). Subtype elimination
      // converts this initially to (and (> x 0.0) (> y 0)), (* x (to_real y)),
      // which is not a valid proof step since y does not match (to_real y).
      // This further converts the arguments to
      // (and (> x 0.0) (> (to_real y) 0.0)), (* x (to_real y)).
      Assert(cargs.size() == 2 && cargs[1].getKind() == Kind::NONLINEAR_MULT);
      std::vector<Node> premise;
      if (cargs[0].getKind() == Kind::AND)
      {
        premise.insert(premise.end(), cargs[0].begin(), cargs[0].end());
      }
      else
      {
        premise.push_back(cargs[0]);
      }
      // map premises to their index
      std::map<Node, size_t> premiseIndex;
      for (size_t i = 0, nprem = premise.size(); i < nprem; i++)
      {
        Node p = premise[i];
        bool neg = p.getKind() == Kind::NOT;
        Node atom = neg ? p[0] : p;
        Assert(atom.getNumChildren() == 2);
        premiseIndex[atom[0]] = i;
      }
      std::vector<Node> nconj;
      bool childChanged = false;
      // for each to_real(x) in the monomial, go back and modify the premise
      // x ~ 0 to to_real(x) ~ 0.0
      std::map<Node, size_t>::iterator itp;
      for (size_t i = 0, nchild = cargs[1].getNumChildren(); i < nchild; i++)
      {
        if (cargs[1][i].getKind() == Kind::TO_REAL)
        {
          itp = premiseIndex.find(cargs[1][i][0]);
          Assert(itp != premiseIndex.end());
          Node p = premise[itp->second];
          bool neg = p.getKind() == Kind::NOT;
          Node atom = neg ? p[0] : p;
          Assert(atom[1].isConst() && atom[1].getConst<Rational>().sgn() == 0);
          childChanged = true;
          Node newAtom = nm->mkNode(
              atom.getKind(), cargs[1][i], nm->mkConstReal(Rational(0)));
          newAtom = neg ? newAtom.notNode() : newAtom;
          premise[itp->second] = newAtom;
        }
      }
      if (childChanged)
      {
        cargs[0] = nm->mkAnd(premise);
      }
    }
    break;
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
    {
      if (cargs[0].getType().isInteger())
      {
        // real relation multiplied by integer, cast the multiplicand to real
        Assert(cargs.size() == 2 && cargs[1].getNumChildren() == 2);
        if (cargs[1][0].getType().isReal())
        {
          cargs[0] = theory::arith::castToReal(nm, cargs[0]);
        }
      }
      else if (cargs[1][0].getType().isInteger())
      {
        // integer relation multiplied by real, cast to a real relation
        cargs[1] = nm->mkNode(cargs[1].getKind(),
                              theory::arith::castToReal(nm, cargs[1][0]),
                              theory::arith::castToReal(nm, cargs[1][1]));
      }
    }
    break;
    default: break;
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
      // a rational, or multiply a real relation by an integer.
      // Note that we modify the arguments to the proof rule above
      // to ensure that the initial rule attempt does not use mixed arithmetic.
      // We transform the proof for the former as follows:
      //
      //            ----- ASSUME
      //            t~s
      // --- ASSUME ----- prove, using method below
      // c>0.0      t'~s'
      // --------------- AND_INTRO ------------------------------ ARITH_MULT_X
      // (and c>0.0 t'~s')           (=> (and c>0 t'~s') (c*t'~c*s'))
      // ----------------------------------------------------- MODUS_PONENS
      // (c*t'~c*s')
      // ------------------------------- SCOPE {c>0.0, t~s}
      // (=> (and c>0.0 t~s) (c*t'~c*s'))
      //
      // there t~s is the original predicate over the integers we had as input
      // and t'~s' is an equivalent predicate over reals. The latter case
      // (multiplying a real relation by an integer) is handled similarly.
      bool csuccess = true;
      // transform the inputs to AND_INTRO
      for (size_t i = 0; i < 2; i++)
      {
        Node relOld = resc[0][i];
        Trace("pf-subtype-elim") << "Old relation: " << relOld << std::endl;
        Node relNew = newRes[0][i];
        Trace("pf-subtype-elim") << "New relation: " << relNew << std::endl;
        if (!prove(relOld, relNew, cdp))
        {
          csuccess = false;
          break;
        }
      }
      // construct the rest of the proof
      if (csuccess)
      {
        cdp->addStep(newRes, id, {}, {cargs[0], newRes[0][1]});
        cdp->addStep(
            newRes[0], ProofRule::AND_INTRO, {newRes[0][0], newRes[0][1]}, {});
        cdp->addStep(
            newRes[1], ProofRule::MODUS_PONENS, {newRes[0], newRes}, {});
        if (prove(newRes[1], resc[1], cdp))
        {
          cdp->addStep(
              resc, ProofRule::SCOPE, {resc[1]}, {resc[0][0], resc[0][1]});
          success = true;
        }
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
    default:
    {
      std::vector<Node> matchConds;
      expr::getConversionConditions(newRes, resc, matchConds);
      // Otherwise find a set of equalities that suffice to show the difference,
      // and use conversion proof generator. For example if we have
      // (= x (to_real 0)) but need (= x 0.0), then matchConds contains
      // { (= (to_real 0) 0.0) }.
      TConvProofGenerator tcpg(d_env,
                               nullptr,
                               TConvPolicy::ONCE,
                               TConvCachePolicy::NEVER,
                               "SubtypeElimConvert",
                               nullptr,
                               true);
      for (const Node& mc : matchConds)
      {
        tcpg.addRewriteStep(mc[0],
                            mc[1],
                            nullptr,
                            true,
                            TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
      }
      std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(newRes);
      Node resr = pfn->getResult();
      Assert(resr.getKind() == Kind::EQUAL);
      if (resr[1] == resc)
      {
        // if successful we have
        // P
        // --  ------ by term conversion + rewrite steps
        // Q   Q = R
        // ---------- EQ_RESOLVE
        // R
        // where P is the premises of this step after subtype elimination,
        // Q is what is proven by the original rule and P, and R is the original
        // conclusion after subtype elimination.
        cdp->addProof(pfn);
        cdp->addStep(resc, ProofRule::EQ_RESOLVE, {newRes, resr}, {});
        cdp->addStep(newRes, id, children, cargs);
      }
    }
    break;
  }
  if (!success)
  {
    // if we did not succeed, just add a trust step
    Trace("pf-subtype-elim-warn")
        << "WARNING: Introduction of subtyping via rule " << id << std::endl;
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
