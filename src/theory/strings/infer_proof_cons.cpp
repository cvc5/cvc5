/*********************                                                        */
/*! \file infer_proof_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference to proof conversion
 **/

#include "theory/strings/infer_proof_cons.h"

#include "expr/proof_skolem_cache.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(eq::ProofEqEngine& pfee,
                               SequencesStatistics& statistics,
                               bool pfEnabled,
                               ProofChecker* pc)
    : d_checker(pc),
      d_pfee(pfee),
      d_statistics(statistics),
      d_pfEnabled(pfEnabled)
{
}

void InferProofCons::convert(InferInfo& ii,
                             std::vector<eq::ProofInferInfo>& piis)
{
  if (ii.d_conc.getKind() == AND)
  {
    Node conj = ii.d_conc;
    for (const Node& cc : conj)
    {
      ii.d_conc = cc;
      convert(ii, piis);
    }
    ii.d_conc = conj;
    return;
  }
  eq::ProofInferInfo pii;
  convert(ii, pii);
  piis.push_back(pii);
}

PfRule InferProofCons::convert(const InferInfo& ii, eq::ProofInferInfo& pii)
{
  return convert(ii.d_id, ii.d_idRev, ii.d_conc, ii.d_ant, ii.d_antn, pii);
}

PfRule InferProofCons::convert(Inference infer,
                               bool isRev,
                               Node conc,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& expn,
                               eq::ProofInferInfo& pii)
{
  // the conclusion is the same
  pii.d_conc = conc;
  // must flatten children with respect to AND to be ready to explain
  for (const Node& ec : exp)
  {
    utils::flattenOp(AND, ec, pii.d_children);
  }
  if (options::stringRExplainLemmas())
  {
    // these are the explained subset of exp, notice that the order of this
    // vector does not matter for proofs
    pii.d_childrenToExplain.insert(pii.d_childrenToExplain.end(),
                                   pii.d_children.begin(),
                                   pii.d_children.end());
  }
  // now, go back and add the unexplained ones
  for (const Node& ecn : expn)
  {
    utils::flattenOp(AND, ecn, pii.d_children);
  }
  // only keep stats if we process it here
  d_statistics.d_inferences << infer;
  if (!d_pfEnabled)
  {
    // don't care about proofs, return now
    return PfRule::UNKNOWN;
  }
  // debug print
  if (Trace.isOn("strings-ipc-debug"))
  {
    Trace("strings-ipc-debug") << "InferProofCons::convert: " << infer
                               << (isRev ? " :rev " : " ") << conc << std::endl;
    for (const Node& ec : exp)
    {
      Trace("strings-ipc-debug") << "    e: " << ec << std::endl;
    }
    for (const Node& ecn : expn)
    {
      Trace("strings-ipc-debug") << "  e-n: " << ecn << std::endl;
    }
  }
  // try to find a proof rule to incorporate
  ProofRuleChecker* tryChecker = nullptr;
  NodeManager * nm = NodeManager::currentNM();
  switch (infer)
  {
    // ========================== equal by substitution+rewriting
    case Inference::I_NORM_S:
    case Inference::I_CONST_MERGE:
    case Inference::I_NORM:
    case Inference::LEN_NORM:
    case Inference::NORMAL_FORM:
    case Inference::CODE_PROXY:
    {
      pii.d_args.push_back(conc);
      // will attempt this rule
      pii.d_rule = PfRule::MACRO_SR_PRED_INTRO;
      tryChecker = &d_builtinChecker;
    }
    break;
    // ========================== substitution + rewriting
    case Inference::RE_NF_CONFLICT:
    case Inference::EXTF:
    case Inference::EXTF_N:
    {
      if (conc.getKind() != EQUAL)
      {
        // use the predicate version
        pii.d_args.push_back(conc);
        pii.d_rule = PfRule::MACRO_SR_PRED_INTRO;
        tryChecker = &d_builtinChecker;
      }
      else
      {
        // minor optimization: apply to LHS of equality (RHS is already reduced)
        // although notice the case above is also a valid proof.
        pii.d_args.push_back(conc[0]);
        pii.d_rule = PfRule::MACRO_SR_EQ_INTRO;
        tryChecker = &d_builtinChecker;
      }
    }
    break;
    // ========================== substitution+rewriting+Boolean entailment
    case Inference::EXTF_D:
    case Inference::EXTF_D_N: break;
    // ========================== equal by substitution+rewriting+rewrite pred
    case Inference::I_CONST_CONFLICT: break;
    // ========================== rewrite pred
    case Inference::EXTF_EQ_REW:
    case Inference::INFER_EMP:
    {
      // may need the "extended equality rewrite"
      pii.d_rule = PfRule::MACRO_SR_PRED_ELIM;
      tryChecker = &d_ufChecker;
    }
    break;
    // ========================== equal by substitution+rewriting+CTN_NOT_EQUAL
    case Inference::F_NCTN:
    case Inference::N_NCTN: break;
    // ========================== substitution+rewriting, CONCAT_EQ, ...
    case Inference::F_CONST:
    case Inference::F_UNIFY:
    case Inference::F_ENDPOINT_EMP:
    case Inference::F_ENDPOINT_EQ:
    case Inference::N_ENDPOINT_EMP:
    case Inference::N_UNIFY:
    case Inference::N_ENDPOINT_EQ:
    case Inference::N_CONST:
    case Inference::SSPLIT_CST_PROP:
    case Inference::SSPLIT_VAR_PROP:
    case Inference::SSPLIT_CST:
    case Inference::SSPLIT_VAR:
    case Inference::DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
    case Inference::DEQ_DISL_STRINGS_SPLIT:
    {
      Trace("strings-ipc-core") << "Generate core rule for " << infer
                                << " (rev=" << isRev << ")" << std::endl;
      // EXP ^ t = s ^ ...
      size_t nchild = pii.d_children.size();
      size_t mainEqIndex = 0;
      bool mainEqIndexSet = false;
      if (infer == Inference::N_UNIFY)
      {
        if (nchild >= 2)
        {
          mainEqIndex = nchild - 2;
          mainEqIndexSet = true;
        }
      }
      else if (infer == Inference::N_ENDPOINT_EQ)
      {
        if (nchild >= 1)
        {
          mainEqIndex = nchild - 1;
          mainEqIndexSet = true;
        }
      }
      Node mainEq;
      if (mainEqIndexSet)
      {
        mainEq = pii.d_children[mainEqIndex];
        Trace("strings-ipc-core") << "Main equality " << mainEq << " at index "
                                  << mainEqIndex << std::endl;
      }
      if (mainEq.isNull() || mainEq.getKind() != EQUAL)
      {
        Trace("strings-ipc-core")
            << "...failed to find main equality" << std::endl;
        // Assert(false);
      }
      else
      {
        // apply MACRO_SR_PRED_ELIM using equalities up to the main eq
        std::vector<Node> childrenSRew;
        childrenSRew.push_back(mainEq);
        childrenSRew.insert(childrenSRew.end(),
                       pii.d_children.begin(),
                       pii.d_children.begin() + mainEqIndex);
        std::reverse(childrenSRew.begin(), childrenSRew.end());
        std::vector<Node> argsSRew;
        Node mainEqSRew = d_ufChecker.check(PfRule::MACRO_SR_PRED_ELIM, childrenSRew, argsSRew);
        Trace("strings-ipc-core")
            << "Main equality after subs+rewrite " << mainEqSRew << std::endl;
        // now, apply CONCAT_EQ to get the remainder
        std::vector<Node> childrenCeq;
        childrenCeq.push_back(mainEqSRew);
        std::vector<Node> argsCeq;
        argsCeq.push_back(nm->mkConst(isRev));
        Node mainEqCeq = d_strChecker.check(PfRule::CONCAT_EQ, childrenCeq, argsCeq);
        Trace("strings-ipc-core")
            << "Main equality after CONCAT_EQ " << mainEqCeq << std::endl;
        
      }
    }
    break;
    // ========================== Boolean split
    case Inference::CARD_SP:
    case Inference::LEN_SPLIT:
    case Inference::LEN_SPLIT_EMP:
    case Inference::DEQ_DISL_EMP_SPLIT:
    case Inference::DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
    case Inference::DEQ_STRINGS_EQ:
    case Inference::DEQ_LENS_EQ:
    case Inference::DEQ_LENGTH_SP:
    {
      if (conc.getKind() != OR)
      {
        Assert(false);
      }
      else
      {
        pii.d_args.push_back(conc[0]);
        tryChecker = &d_boolChecker;
      }
    }
    break;
    // ========================== Regular expression unfolding
    case Inference::RE_UNFOLD_POS:
    case Inference::RE_UNFOLD_NEG: {
    }
    break;
    // ========================== Reduction
    case Inference::CTN_POS: break;
    case Inference::REDUCTION:
    {
      size_t nchild = conc.getNumChildren();
      if (conc.getKind() != AND || conc[nchild - 1].getKind() != EQUAL)
      {
        Assert(false);
      }
      else
      {
        pii.d_rule = PfRule::REDUCTION;
        // the left hand side of the last conjunct is the term we are reducing
        pii.d_args.push_back(conc[nchild - 1][0]);
        tryChecker = &d_strChecker;
      }
    }
    break;
    // ========================== Cardinality
    case Inference::CARDINALITY: break;
    // ========================== code injectivity
    case Inference::CODE_INJ: break;

    // ========================== unknown
    case Inference::I_CYCLE_E:
    case Inference::I_CYCLE:
    case Inference::RE_DELTA:
    case Inference::RE_DELTA_CONF:
    case Inference::RE_DERIVE:
    case Inference::FLOOP:
    case Inference::FLOOP_CONFLICT: break;

    // FIXME
    case Inference::DEQ_NORM_EMP:
    case Inference::RE_INTER_INCLUDE:
    case Inference::RE_INTER_CONF:
    case Inference::RE_INTER_INFER:
    case Inference::CTN_TRANS:
    case Inference::CTN_DECOMPOSE:
    case Inference::CTN_NEG_EQUAL:
    default: break;
  }

  // now see if we would succeed with the checker-to-try
  if (tryChecker != nullptr)
  {
    Trace("strings-ipc") << "For " << infer << ", try proof rule " << pii.d_rule
                         << "...";
    Assert(pii.d_rule != PfRule::UNKNOWN);
    Node pconc = tryChecker->check(pii.d_rule, pii.d_children, pii.d_args);
    if (pconc.isNull() || pconc != conc)
    {
      Trace("strings-ipc") << "failed, pconc is " << pconc << " (expected "
                           << conc << ")" << std::endl;
      pii.d_rule = PfRule::UNKNOWN;
    }
    else
    {
      Trace("strings-ipc") << "success!" << std::endl;
    }
  }
  else
  {
    Trace("strings-ipc") << "For " << infer << " " << conc
                         << ", no proof rule, failed" << std::endl;
    Assert(pii.d_rule == PfRule::UNKNOWN);
  }

  if (pii.d_rule == PfRule::UNKNOWN)
  {
    // debug print
    if (Trace.isOn("strings-ipc-fail"))
    {
      Trace("strings-ipc-fail")
          << "InferProofCons::convert: Failed " << infer
          << (isRev ? " :rev " : " ") << conc << std::endl;
      for (const Node& ec : exp)
      {
        Trace("strings-ipc-fail") << "    e: " << ec << std::endl;
      }
      for (const Node& ecn : expn)
      {
        Trace("strings-ipc-fail") << "  e-n: " << ecn << std::endl;
      }
    }
    // untrustworthy conversion
    // doesn't expect arguments
    pii.d_args.clear();
    // rule is determined automatically
    pii.d_rule =
        static_cast<PfRule>(static_cast<uint32_t>(PfRule::SIU_BEGIN)
                            + (static_cast<uint32_t>(infer)
                               - static_cast<uint32_t>(Inference::BEGIN)));
    // add to stats
    d_statistics.d_inferencesNoPf << infer;
  }
  if (Trace.isOn("strings-ipc-debug"))
  {
    Trace("strings-ipc-debug")
        << "InferProofCons::convert returned " << pii << std::endl;
  }
  return pii.d_rule;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
