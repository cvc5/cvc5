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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(eq::ProofEqEngine& pfee,
                               SequencesStatistics& statistics,
                               bool pfEnabled)
    : d_pfee(pfee), d_statistics(statistics), d_pfEnabled(pfEnabled)
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
    // these are the explained ones
    pii.d_childrenExp.insert(
        pii.d_childrenExp.end(), pii.d_children.begin(), pii.d_children.end());
  }
  for (const Node& ecn : expn)
  {
    utils::flattenOp(AND, ecn, pii.d_children);
  }
  // only keep stats if we process it here
  d_statistics.d_inferences << infer;
  /*
  if (!d_pfEnabled)
  {
    // don't care about proofs, return now
    return;
  }
  */
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
  bool success = false;

  if (!success)
  {
    // untrustworthy conversion
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
