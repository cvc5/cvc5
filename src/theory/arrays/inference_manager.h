/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arrays inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__INFERENCE_MANAGER_H
#define CVC4__THEORY__ARRAYS__INFERENCE_MANAGER_H

#include "expr/node.h"
#include "expr/proof_rule.h"
#include "theory/theory_inference_manager.h"

namespace CVC4 {
namespace theory {
namespace arrays {

/**
 * The arrays inference manager
 */
class InferenceManager : public TheoryInferenceManager
{
 public:
  InferenceManager(Theory& t, TheoryState& state, ProofNodeManager* pnm);
  ~InferenceManager() {}

  /** Assert inference internal */
  bool assertInference(TNode eq, bool polarity, TNode reason, PfRule r);
};

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

#endif
