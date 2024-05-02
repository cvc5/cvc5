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
    : EnvObj(env), d_tsr(tsr), d_imap(userContext()), d_expMap(userContext())
{
  d_false = nodeManager()->mkConst(false);
  d_tid = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_SETS);
}

void InferProofCons::notifyFact(const Node& conc,
                                const Node& exp,
                                InferenceId id)
{
  Assert(conc.getKind() != Kind::AND && conc.getKind() != Kind::IMPLIES);
  d_imap[conc] = id;
  d_expMap[conc] = exp;
}

void InferProofCons::notifyConflict(const Node& conf, InferenceId id)
{
  d_imap[conf.notNode()] = id;
}

void InferProofCons::notifyLemma(const Node& lem, InferenceId id)
{
  d_imap[lem] = id;
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  NodeInferenceMap::iterator it = d_imap.find(fact);
  Assert(it != d_imap.end());
  InferenceId id = it->second;

  // temporary proof
  CDProof cdp(d_env);
  std::vector<Node> assumps;
  Node conc = fact;
  // run the conversion
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
  if (!convert(cdp, id, assumps, conc))
  {
    cdp.addTrustedStep(conc, TrustId::THEORY_INFERENCE, assumps, {d_tid});
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
      // (and (set.member x S) (= S (op T1 T2))) =>
      // rewrite((set.member x (op T1 T2)))
      // this holds by applying the equality as a substitution to the first
      // assumption and rewriting.
      std::vector<Node> exp(assumps.begin() + 1, assumps.end());
      Node aelim = psb.applyPredElim(assumps[0], exp);
      success = (aelim == conc);
      Assert(success);
    }
    break;
    case InferenceId::SETS_UP_CLOSURE:
    case InferenceId::SETS_UP_CLOSURE_2:
    {
      NodeManager* nm = nodeManager();
      Assert(conc.getKind() == Kind::SET_MEMBER);
      Node so = SkolemManager::getUnpurifiedForm(conc[1]);
      Trace("sets-ipc") << "Unpurified form " << so << std::endl;
      Node memo = nm->mkNode(Kind::SET_MEMBER, conc[0], so);
      Node memor = d_tsr->rewriteMembershipBinaryOp(memo);
      Trace("sets-ipc") << "Single step rewriting of membership " << memor
                        << std::endl;
      Assert(memo != memor);
      // collect the memberships in the premise
      std::vector<Node> assumpMem;
      std::vector<Node> assumpOther;
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
      Node msrc;
      if (assumpMem.size() == 2)
      {
        msrc = nm->mkAnd(assumpMem);
        psb.addStep(ProofRule::AND_INTRO, {assumpMem}, {}, msrc);
      }
      else
      {
        msrc = assumpMem[0];
      }
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
            success = psb.applyPredIntro(memor, {mtgt}, MethodId::SB_FORMULA);
            Assert(success);
          }
          Trace("sets-ipc") << "......success" << std::endl;
          break;
        }
      }
      if (!success)
      {
        Assert(success);
        break;
      }
      Trace("sets-ipc") << "* Prove transform " << memor << " to " << memo
                        << std::endl;
      if (!psb.applyPredTransform(memor, memo, {}))
      {
        success = false;
        Assert(success);
        break;
      }
      if (so != conc[1])
      {
        std::vector<Node> ceqs;
        Node ceq = conc[0].eqNode(conc[0]);
        if (!psb.addStep(ProofRule::REFL, {}, {conc[0]}, ceq))
        {
          success = false;
          Assert(success);
          break;
        }
        ceqs.push_back(ceq);
        ceq = so.eqNode(conc[1]);
        Trace("sets-ipc") << "* Prove equal (by original forms) " << ceq
                          << std::endl;
        if (!psb.addStep(ProofRule::MACRO_SR_PRED_INTRO, {}, {ceq}, ceq))
        {
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
          success = false;
          Assert(success);
          break;
        }
        if (!psb.addStep(ProofRule::EQ_RESOLVE, {memo, cequiv}, {}, conc))
        {
          success = false;
          Assert(success);
          break;
        }
      }
    }
    break;
    case InferenceId::SETS_SKOLEM:
    {
      Assert (assumps.empty());
      success = psb.applyPredIntro(conc, {});
      Assert(success);
    }
    break;
    case InferenceId::SETS_DEQ:
    {
      Assert(assumps.size() == 1);
      Node res = psb.tryStep(ProofRule::SETS_EXT, {assumps[0]}, {}, conc);
      success = (res == conc);
      Assert(success);
    }
    break;
    case InferenceId::SETS_SINGLETON_EQ:
    {
      // SINGLETON_INJ
      Assert(assumps.size() == 1);
      Node res =
          psb.tryStep(ProofRule::SETS_SINGLETON_INJ, {assumps[0]}, {}, conc);
      success = (res == conc);
      Assert(success);
    }
    break;
    case InferenceId::SETS_EQ_CONFLICT:
    case InferenceId::SETS_EQ_MEM_CONFLICT:
    case InferenceId::SETS_EQ_MEM:
    {
      AlwaysAssert(false) << "Unhandled " << id;
    }
    break;
    default: break;
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
  // AlwaysAssert(success);
  return success;
}

std::string InferProofCons::identify() const { return "sets::InferProofCons"; }

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
