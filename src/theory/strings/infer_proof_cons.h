/*********************                                                        */
/*! \file infer_proof_cons.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference to proof conversion
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H
#define CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H

#include <vector>

#include "expr/proof_rule.h"
#include "expr/node.h"
#include "theory/strings/infer_info.h"
#include "theory/uf/proof_equality_engine.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Converts between Inference and information needed to provide a proof step 
 * (PfRule, children, args).
 */
class InferProofCons
{
public:
  InferProofCons(ProofEqualityEngine& pfee);
  ~InferProofCons(){}
  /** convert
   * 
   * This method is called when the theory of strings makes an inference
   * described by the first four arguments (exp, expn, eq, infer).
   * 
   * This method converts this call to a proof step consisting of
   * (1) A returned proof rule identifier.
   * (2) The premises of the proof step (pfChildren).
   * (3) Arguments to the proof step (pfArgs).
  */
  PfRule convert(const std::vector<Node>& exp,
                                     const std::vector<Node>& expn,
                                     Node eq,
                                     Inference infer,
                                     std::vector<Node>& pfChildren,
                 std::vector<Node>& pfArgs
                );
private:
  /** The proof-producing equality engine */
  ProofEqualityEngine& d_pfee;
};
  
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H */
