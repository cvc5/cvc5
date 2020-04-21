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

PfRule InferProofCons::convert(const InferInfo& ii,
                               std::vector<Node>& pfChildren,
                               std::vector<Node>& pfExp,
                               std::vector<Node>& pfArgs)
{
  return convert(
      ii.d_id, ii.d_conc, ii.d_ant, ii.d_antn, pfChildren, pfExp, pfArgs);
}

PfRule InferProofCons::convert(Inference infer,
                               Node conc,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& expn,
                               std::vector<Node>& pfChildren,
                               std::vector<Node>& pfExp,
                               std::vector<Node>& pfArgs)
{
  // must flatten children with respect to AND to be ready to explain
  for (const Node& ec : exp)
  {
    utils::flattenOp(AND, ec, pfChildren);
  }
  if (options::stringRExplainLemmas())
  {
    // these are the explained ones
    pfExp.insert(pfExp.end(), pfChildren.begin(), pfChildren.end());
  }
  for (const Node& ecn : expn)
  {
    utils::flattenOp(AND, ecn, pfChildren);
  }
  // only keep stats if we process it here
  d_statistics.d_inferences << infer;
  /*
  if (!d_pfEnabled)
  {
    // don't care about proofs, return now
    return PfRule::UNKNOWN;
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

  return PfRule::UNKNOWN;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
