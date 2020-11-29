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

#include "context/cdhashmap.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/operator_elim.h"
#include "theory/logic_info.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * This module can be used for (on demand) elimination of extended arithmetic
 * operators like div, mod, to_int, is_int, sqrt, and so on. It uses the
 * operator elimination utility for determining how to reduce formulas. It
 * extends that utility with the ability to generate lemmas on demand via
 * the provided inference manager.
 */
class ArithPreprocess
{
 public:
  ArithPreprocess(ArithState& state,
                  InferenceManager& im,
                  ProofNodeManager* pnm,
                  const LogicInfo& info);
  ~ArithPreprocess() {}
  /**
   * Call eliminate operators on formula n, return the resulting trust node,
   * which is of TrustNodeKind REWRITE and whose node is the result of
   * eliminating extended operators from n.
   */
  TrustNode eliminate(TNode n);
  /**
   * Reduce assertion. This sends a lemma via the inference manager if atom
   * contains any extended operators. When applicable, the lemma is of the form:
   *   atom == d_opElim.eliminate(atom)
   * This method returns true if a lemma of the above form was added to
   * the inference manager. Note this returns true even if this lemma was added
   * on a previous call.
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
  context::CDHashMap<Node, bool, NodeHashFunction> d_reduced;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
