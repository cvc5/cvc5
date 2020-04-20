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

#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(eq::ProofEqEngine& pfee) : d_pfee(pfee) {}

PfRule InferProofCons::convert(const InferInfo& ii,
                               std::vector<Node>& pfChildren,
                               std::vector<Node>& pfArgs)
{
  return convert(ii.d_id, ii.d_conc, ii.d_ant, ii.d_antn, pfChildren, pfArgs);
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
  pfExp.insert(pfExp.end(), pfChildren.begin(), pfChildren.end());
  for (const Node& ecn : expn)
  {
    utils::flattenOp(AND, ecn, pfChildren);
  }
  return PfRule::UNKNOWN;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
