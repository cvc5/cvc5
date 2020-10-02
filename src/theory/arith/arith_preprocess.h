/*********************                                                        */
/*! \file arith_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic preprocess
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_PREPROCESS_H
#define CVC4__THEORY__ARITH__ARITH_PREPROCESS_H

#include "context/cdhashset.h"
#include "theory/arith/operator_elim.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/inference_manager.h"
#include "theory/logic_info.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithPreprocess
{
 public:
  ArithPreprocess(ArithState& state, InferenceManager& im, ProofNodeManager* pnm, const LogicInfo& info);
  ~ArithPreprocess() {}
  /** 
   * Reduce assertion. This sends a lemma via the inference manager if atom
   * contains any extended operators. When applicable, the lemma is of the form:
   *   atom == d_opElim.eliminate(atom)
   */
  bool reduceAssertion(TNode atom);
  /** 
   * Is the atom reduced? Returns true if a call to method reduceAssertion was
   * made for the given atom and returned a lemma. In this case, the atom
   * can be ignored.
   */
  bool isReduced(TNode atom) const;
 private:
  /** Reference to the inference manager */
  InferenceManager& d_im;
  /** The operator elimination utility */
  OperatorElim d_opElim;
  /** The set of assertions that were reduced */
  context::CDHashSet<Node, NodeHashFunction> d_reduced;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
