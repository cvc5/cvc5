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

#include "options/strings_options.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(eq::ProofEqEngine& pfee,
                               SequencesStatistics& statistics,
                               bool pfEnabled,
                 ProofChecker * pc)
    : d_checker(pc), d_pfee(pfee), d_statistics(statistics), d_pfEnabled(pfEnabled)
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
  convert(ii.d_id, ii.d_conc, ii.d_ant, ii.d_antn, pii);
  piis.push_back(pii);
}

PfRule InferProofCons::convert(const InferInfo& ii, eq::ProofInferInfo& pii)
{
  return convert(ii.d_id, ii.d_conc, ii.d_ant, ii.d_antn, pii);
}

PfRule InferProofCons::convert(Inference infer,
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
    // these are the explained ones, notice that the order of this vector does
    // not matter
    pii.d_childrenToExplain.insert(
        pii.d_childrenToExplain.end(), pii.d_children.begin(), pii.d_children.end());
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
  if (Trace.isOn("strings-ipc"))
  {
    Trace("strings-ipc") << "InferProofCons::convert: " << infer << " " << conc
                         << std::endl;
    for (const Node& ec : exp)
    {
      Trace("strings-ipc") << "    e: " << ec << std::endl;
    }
    for (const Node& ecn : expn)
    {
      Trace("strings-ipc") << "  e-n: " << ecn << std::endl;
    }
  }
  // try to find a proof rule to incorporate
  ProofRuleChecker * tryChecker = nullptr;
  switch(infer)
  {
  // ========================== equal by substitution+rewriting
  case Inference::I_NORM_S :
  case Inference::I_CONST_MERGE :
  case Inference::I_NORM :
  case Inference::LEN_NORM :
  case Inference::NORMAL_FORM :
  {
    if (pii.d_children.empty())
    {
      // should have at least one child
    }
    else if (conc.getKind()!=EQUAL)
    {
      Assert(false);
    }
    else
    {
      // substitutions applied in reverse order?
      //std::reverse(pii.d_children.begin(), pii.d_children.end());
      pii.d_args.push_back(conc[0]);
      pii.d_args.push_back(conc[1]);
      // will attempt this rule
      pii.d_rule = PfRule::MACRO_EQ_SUBS_REWRITE;
      tryChecker = &d_ufChecker;
    }
  }
    break;
  // ========================== substitution + rewriting
  case Inference::RE_NF_CONFLICT :
  case Inference::EXTF :
  case Inference::EXTF_N :
  {
    if (pii.d_children.empty())
    {
      // should have at least one child
    }
    else if (conc.getKind()!=EQUAL)
    {
      //Assert(false);
      // predicate case, convert = true|false
    }
    else
    {
      // substitutions applied in reverse order?
      //std::reverse(pii.d_children.begin(), pii.d_children.end());
      pii.d_args.push_back(conc[0]);
      // will attempt this rule
      pii.d_rule = PfRule::SUBS_REWRITE;
      tryChecker = &d_builtinChecker;
    }
  }
    break;
  // ========================== substitution+rewriting+Boolean entailment
  case Inference::EXTF_D :
  case Inference::EXTF_D_N :
    break;
  // ========================== equal by substitution+rewriting+rewrite pred
  case Inference::I_CONST_CONFLICT :
    break;
  // ========================== rewrite pred
  case Inference::EXTF_EQ_REW :
  case Inference::INFER_EMP :
    break;
  // ========================== equal by substitution+rewriting+CTN_NOT_EQUAL
  case Inference::F_NCTN :
  case Inference::N_NCTN :
    break;
  // ========================== substitution+rewriting, CONCAT_EQ, ...
  case Inference::F_CONST :
  case Inference::F_UNIFY :
  case Inference::F_ENDPOINT_EMP :
  case Inference::F_ENDPOINT_EQ :
  case Inference::N_ENDPOINT_EMP :
  case Inference::N_UNIFY :
  case Inference::N_ENDPOINT_EQ :
  case Inference::N_CONST :
  case Inference::SSPLIT_CST_PROP :
  case Inference::SSPLIT_VAR_PROP :
  case Inference::SSPLIT_CST :
  case Inference::SSPLIT_VAR :
  case Inference::DEQ_DISL_FIRST_CHAR_STRING_SPLIT :
  case Inference::DEQ_DISL_STRINGS_SPLIT :
    break;
  // ========================== Boolean split
  case Inference::CARD_SP :
  case Inference::LEN_SPLIT :
  case Inference::LEN_SPLIT_EMP :
  case Inference::DEQ_DISL_EMP_SPLIT :
  case Inference::DEQ_DISL_FIRST_CHAR_EQ_SPLIT :
  case Inference::DEQ_STRINGS_EQ :
  case Inference::DEQ_LENS_EQ :
  case Inference::DEQ_LENGTH_SP :
  {
    if (conc.getKind()!=OR)
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
  case Inference::RE_UNFOLD_POS :
    break;
  case Inference::RE_UNFOLD_NEG :
    break;
  // ========================== Reduction
  case Inference::CTN_POS :
    break;
  case Inference::REDUCTION :
    break;
  // ========================== Cardinality
  case Inference::CARDINALITY :
    break;
  // ========================== purification
  case Inference::CODE_PROXY :    
    break;
  // ========================== code injectivity
  case Inference::CODE_INJ :
    break;
    
  // ========================== unknown
  case Inference::I_CYCLE_E :
  case Inference::I_CYCLE :
  case Inference::RE_DELTA :
  case Inference::RE_DELTA_CONF :
  case Inference::RE_DERIVE :
  case Inference::FLOOP :
  case Inference::FLOOP_CONFLICT :
    break;
    
  // FIXME
  case Inference::DEQ_NORM_EMP :
  case Inference::RE_INTER_INCLUDE :
  case Inference::RE_INTER_CONF :
  case Inference::RE_INTER_INFER :
  case Inference::CTN_TRANS :
  case Inference::CTN_DECOMPOSE :
  case Inference::CTN_NEG_EQUAL :
  default:
    
    break;
  }
  
  // now see if we would succeed with the checker-to-try
  if (tryChecker!=nullptr)
  {
    Trace("strings-ipc") << "For " << infer << ", try proof rule "<< pii.d_rule << "...";
    Assert (pii.d_rule!=PfRule::UNKNOWN);
    Node pconc = tryChecker->check(pii.d_rule,pii.d_children,pii.d_args);
    if (pconc.isNull() || pconc!=conc)
    {
      Trace("strings-ipc") << "failed, pconc is " << pconc << " (expected " << conc << ")" << std::endl;
      pii.d_rule = PfRule::UNKNOWN;
    }
    else
    {
      Trace("strings-ipc") << "success!" << std::endl;
    }
  }
  else
  {
    Assert(pii.d_rule==PfRule::UNKNOWN);
  }

  if (pii.d_rule==PfRule::UNKNOWN)
  {
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
  if (Trace.isOn("strings-ipc"))
  {
    Trace("strings-ipc") << "InferProofCons::convert returned " << pii
                         << std::endl;
  }
  return pii.d_rule;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
