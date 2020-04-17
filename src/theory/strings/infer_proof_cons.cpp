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

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(ProofEqualityEngine& pfee) : d_pfee(pfee)
{
  
}

PfRule InferProofCons::convert(const std::vector<Node>& exp,
                                    const std::vector<Node>& expn,
                                    Node eq,
                                    Inference infer,
                                    std::vector<Node>& pfChildren,
                std::vector<Node>& pfArgs,
                 ProofEqualityEngine& pfee
              )
{
  // TODO
  pfChildren.insert(pfChildren.end(), exp.begin(), exp.end());
  pfChildren.insert(pfChildren.end(), expn.begin(), expn.end());
  return PfRule::UNKNOWN;
}
  
}  // namespace strings
}  // namespace theory
}  // namespace CVC4
