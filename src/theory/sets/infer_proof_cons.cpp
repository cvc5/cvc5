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
 * Inference to proof conversion for sets.
 */

#include "theory/sets/infer_proof_cons.h"

#include "expr/skolem_manager.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "theory/builtin/proof_checker.h"
#include "theory/sets/theory_sets_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

InferProofCons::InferProofCons(Env& env, TheorySetsRewriter* tsr)
    : EnvObj(env),
      d_tsr(tsr),
      d_uimap(userContext()),
      d_fmap(context()),
      d_expMap(context())
{
  d_false = nodeManager()->mkConst(false);
}

void InferProofCons::notifyFact(const Node& conc,
                                const Node& exp,
                                InferenceId id)
{
  Assert(conc.getKind() != Kind::AND && conc.getKind() != Kind::IMPLIES);
  if (d_fmap.find(conc) != d_fmap.end())
  {
    // already exists, redundant
    return;
  }
  d_fmap[conc] = id;
  d_expMap[conc] = exp;
}

void InferProofCons::notifyConflict(const Node& conf, InferenceId id)
{
  Trace("sets-ipc-debug") << "SetsIpc::conflict " << conf << " " << id
                          << std::endl;
  d_uimap[conf.notNode()] = id;
}

void InferProofCons::notifyLemma(const Node& lem, InferenceId id)
{
  Trace("sets-ipc-debug") << "SetsIpc::lemma " << lem << " " << id << std::endl;
  d_uimap[lem] = id;
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  NodeInferenceMap::iterator it = d_uimap.find(fact);
  if (it == d_uimap.end())
  {
    // should be a fact
    it = d_fmap.find(fact);
    Assert(it != d_fmap.end());
  }
  InferenceId id = it->second;

  // temporary proof
  CDProof cdp(d_env);
  std::vector<Node> assumps;
  Node conc = fact;
  // First split into conclusion and assumptions.
  if (fact.getKind() == Kind::IMPLIES || fact.getKind() == Kind::NOT)
  {
    if (fact[0].getKind() == Kind::AND)
    {
      assumps.insert(assumps.begin(), fact[0].begin(), fact[0].end());
    }
    else
    {
      assumps.push_back(fact[0]);
    }
    if (fact.getKind() == Kind::IMPLIES)
    {
      conc = fact[1];
    }
    else
    {
      conc = d_false;
    }
    cdp.addStep(fact, ProofRule::SCOPE, {conc}, {assumps});
  }
  else
  {
    // should be a fact
    NodeExpMap::iterator itex = d_expMap.find(fact);
    if (itex != d_expMap.end())
    {
      Node exp = itex->second;
      if (exp.getKind() == Kind::AND)
      {
        assumps.insert(assumps.end(), exp.begin(), exp.end());
      }
      else
      {
        assumps.push_back(exp);
      }
    }
  }
  // Try to convert.
  if (!convert(cdp, id, assumps, conc))
  {
    cdp.addTrustedStep(conc, TrustId::THEORY_INFERENCE_SETS, assumps, {});
  }
  return cdp.getProofFor(fact);
}

bool InferProofCons::convert(CDProof& cdp,
                             InferenceId id,
                             const std::vector<Node>& assumps,
                             const Node& conc)
{
  // these are handled manually
  Assert(id != InferenceId::SETS_PROXY
         && id != InferenceId::SETS_PROXY_SINGLETON);
  Trace("sets-ipc") << "InferProofCons::convert " << id << std::endl;
  Trace("sets-ipc") << "- assumptions: " << assumps << std::endl;
  Trace("sets-ipc") << "- conclusion:  " << conc << std::endl;
  bool success = false;
  TheoryProofStepBuffer psb(cdp.getManager()->getChecker(), true);
  switch (id)
  {
    case InferenceId::SETS_DOWN_CLOSURE:
    case InferenceId::SETS_MEM_EQ:
    case InferenceId::SETS_MEM_EQ_CONFLICT:
    {
      Assert(assumps.size() >= 1);
      Assert(assumps[0].getKind() == Kind::SET_MEMBER);
      Assert(assumps.size() == 1 || assumps[1].getKind() == Kind::EQUAL);
      // (and (set.member x S) (= S (op T1 T2))) =>
      // rewrite((set.member x (op T1 T2)))
      // this holds by applying the equality as a substitution to the first
      // assumption and rewriting.
      std::vector<Node> exp(assumps.begin() + 1, assumps.end());
      Node aelim = psb.applyPredElim(assumps[0], exp);
      success = true;
      if (!CDProof::isSame(aelim, conc))
      {
        success = psb.applyPredTransform(aelim, conc, {});
      }
      // should never fail
      Assert(success);
    }
    break;
    case InferenceId::SETS_UP_CLOSURE:
    case InferenceId::SETS_UP_CLOSURE_2:
    {
      NodeManager* nm = nodeManager();
      // An example inference is:
      // (set.member x A) ^ (set.member y B) ^ (= x y) => (set.member x k)
      // where k is the purification skolem for (set.inter A B).
      Assert(conc.getKind() == Kind::SET_MEMBER);
      Node so = SkolemManager::getUnpurifiedForm(conc[1]);
      Trace("sets-ipc") << "Unpurified form " << so << std::endl;
      // We first compute the single step rewriting of the conclusion.
      // For the above example, memor would be:
      // (and (set.member x A) (set.member x B)).
      Node memo = nm->mkNode(Kind::SET_MEMBER, conc[0], so);
      Node memor = d_tsr->rewriteMembershipBinaryOp(memo);
      Trace("sets-ipc") << "Single step rewriting of membership " << memor
                        << std::endl;
      Assert(memo != memor);
      // collect the memberships in the premise
      std::vector<Node> assumpMem;
      std::vector<Node> assumpOther;
      // We now partition the antecedant to the membership
      // part (assumpMem) and the substitution part (assumpOther). The
      // membership part will be equivalent via rewriting to the conclusion.
      for (const Node& a : assumps)
      {
        Node aa = a.getKind() == Kind::NOT ? a[0] : a;
        if (aa.getKind() == Kind::SET_MEMBER)
        {
          assumpMem.push_back(a);
        }
        else
        {
          assumpOther.push_back(a);
        }
      }
      Assert(assumpMem.size() == 1 || assumpMem.size() == 2);
      Node msrc;
      // Use AND_INTRO to put the memberships together if necessary.
      if (assumpMem.size() == 2)
      {
        msrc = nm->mkAnd(assumpMem);
        psb.addStep(ProofRule::AND_INTRO, {assumpMem}, {}, msrc);
      }
      else
      {
        msrc = assumpMem[0];
      }
      // Now, prove the equivalence between the memberships and the
      // conclusion, possibly using the substituion in assumpOther.
      bool isOr = (memor.getKind() == Kind::OR);
      size_t ntgts = isOr ? 2 : 1;
      for (size_t i = 0; i < ntgts; i++)
      {
        Node mtgt = isOr ? memor[i] : memor;
        Trace("sets-ipc") << "...try target " << mtgt << std::endl;
        if (psb.applyPredTransform(msrc, mtgt, assumpOther))
        {
          success = true;
          if (isOr)
          {
            // if union, we get the desired (left or right) conclusion
            success = psb.applyPredIntro(memor, {mtgt}, MethodId::SB_FORMULA);
            // should never fail
            Assert(success);
          }
          Trace("sets-ipc") << "......success" << std::endl;
          break;
        }
      }
      // If successful, we have proven:
      //
      // (set.member x A)   (set.member y B)
      // --------------------------------------- AND_INTRO
      // (and (set.member x A) (set.member y B))    (= x y)
      // ------------------------------------------------- MACRO_SR_PRED_TRANS
      // (set.member x (set.inter A B))
      if (!success)
      {
        Assert(success);
        break;
      }
      // If successful, go back and show memor holds.
      Trace("sets-ipc") << "* Prove transform " << memor << " to " << memo
                        << std::endl;
      if (!psb.applyPredTransform(memor, memo, {}))
      {
        // should never fail
        success = false;
        Assert(success);
        break;
      }
      if (so != conc[1])
      {
        std::vector<Node> ceqs;
        Node ceq = conc[0].eqNode(conc[0]);
        psb.addStep(ProofRule::REFL, {}, {conc[0]}, ceq);
        ceqs.push_back(ceq);
        ceq = so.eqNode(conc[1]);
        Trace("sets-ipc") << "* Prove equal (by original forms) " << ceq
                          << std::endl;
        if (!psb.addStep(ProofRule::MACRO_SR_PRED_INTRO, {}, {ceq}, ceq))
        {
          // should never fail
          success = false;
          Assert(success);
          break;
        }
        ceqs.push_back(ceq);
        std::vector<Node> cargs;
        Node cequiv = memo.eqNode(conc);
        ProofRule cr = expr::getCongRule(memo, cargs);
        if (!psb.addStep(cr, ceqs, cargs, cequiv))
        {
          // should never fail
          success = false;
          Assert(success);
          break;
        }
        if (!psb.addStep(ProofRule::EQ_RESOLVE, {memo, cequiv}, {}, conc))
        {
          // should never fail
          success = false;
          Assert(success);
          break;
        }
      }
      // Final proof now is,using A^B as shorthand for (set.inter A B):
      //
      //                    ----- REFL  ---------- MACRO_SR_PRED_INTRO
      // ...                x = x       A^B = k
      // ------------------ -------------------------------------- CONG
      // (set.member x A^B) (set.member x A^B) = (set.member x k)
      // --------------------------------------------------------- EQ_RESOLVE
      // (set.member x k)
      //
      // where ... is the proof from above.
    }
    break;
    case InferenceId::SETS_SKOLEM:
    {
      Assert(assumps.empty());
      success = psb.applyPredIntro(conc, {});
      Assert(success);
    }
    break;
    case InferenceId::SETS_DEQ:
    {
      Assert(assumps.size() == 1);
      Node exp = assumps[0];
      // ensure we are properly ordered
      Assert(exp.getKind() == Kind::NOT && exp[0].getKind() == Kind::EQUAL
             && exp[0][0] < exp[0][1]);
      Node res = psb.tryStep(ProofRule::SETS_EXT, {exp}, {}, conc);
      success = CDProof::isSame(res, conc);
      Assert(success);
    }
    break;
    case InferenceId::SETS_SINGLETON_EQ:
    {
      // SINGLETON_INJ
      Assert(assumps.size() == 1);
      Node res =
          psb.tryStep(ProofRule::SETS_SINGLETON_INJ, {assumps[0]}, {}, conc);
      success = CDProof::isSame(res, conc);
      Assert(success);
    }
    break;
    case InferenceId::SETS_FILTER_UP:
    case InferenceId::SETS_FILTER_DOWN:
    {
      Node mem = assumps[0];
      if (assumps.size() == 2)
      {
        // Transform based on the second equality A = B:
        //
        //                  ------ REFL
        //                   x = x               A = B
        //                  ----------------------------------- CONG
        // (set.member x A) (set.member x A) = (set.member x B)
        // ---------------------------------------------------- EQ_RESOLVE
        // (set.member x B)
        Assert(assumps[0].getKind() == Kind::SET_MEMBER);
        Assert(assumps[1].getKind() == Kind::EQUAL);
        Node refl = psb.tryStep(ProofRule::REFL, {}, {assumps[0][0]});
        std::vector<Node> cargs;
        ProofRule cr = expr::getCongRule(assumps[0], cargs);
        Node aeq = assumps[1];
        if (aeq[1] == assumps[0][1])
        {
          // flip?
          aeq = aeq[1].eqNode(aeq[0]);
          psb.tryStep(ProofRule::SYMM, {assumps[1]}, {});
        }
        Node eq = psb.tryStep(cr, {refl, aeq}, cargs);
        Trace("sets-ipc") << "...via CONG is " << eq << ", now try with " << mem
                          << std::endl;
        mem = psb.tryStep(ProofRule::EQ_RESOLVE, {mem, eq}, {});
        Assert(!mem.isNull());
      }
      ProofRule pr = (id == InferenceId::SETS_FILTER_UP)
                         ? ProofRule::SETS_FILTER_UP
                         : ProofRule::SETS_FILTER_DOWN;
      std::vector<Node> pfArgs;
      if (id == InferenceId::SETS_FILTER_UP)
      {
        Assert(conc.getKind() == Kind::EQUAL
               && conc[0].getKind() == Kind::SET_MEMBER
               && conc[0][1].getKind() == Kind::SET_FILTER);
        Node pred = conc[0][1][0];
        pfArgs.push_back(pred);
      }
      Node res = psb.tryStep(pr, {mem}, pfArgs);
      Trace("sets-ipc") << "Filter rule " << id << " returns " << res
                        << ", expects " << conc << std::endl;
      success = CDProof::isSame(res, conc);
      Assert(success);
    }
    break;
    case InferenceId::SETS_EQ_MEM_CONFLICT:
    case InferenceId::SETS_EQ_MEM:
    {
      // Handles cases:
      // (and (= S set.empty) (set.member x S)) => false
      // (and (= S (set.singleton y)) (set.member x S)) => (= x y)
      Assert(assumps.size()==2);
      Assert(assumps[0].getKind() == Kind::EQUAL);
      Assert(assumps[1].getKind() == Kind::SET_MEMBER);
      success = psb.applyPredTransform(assumps[1], conc, {assumps[0]});
    }
      break;
    case InferenceId::SETS_EQ_CONFLICT:
    default: Trace("sets-ipc") << "Unhandled " << id; break;
  }
  if (success)
  {
    if (!cdp.addSteps(psb))
    {
      // should not fail if success was computed correctly above
      Assert(false);
      success = false;
    }
  }
  Trace("sets-ipc") << "...success = " << success << std::endl;
  return success;
}

std::string InferProofCons::identify() const { return "sets::InferProofCons"; }

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
