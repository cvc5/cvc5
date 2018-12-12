/*********************                                                        */
/*! \file arith_proof_recorder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class for saving the skeletons of a arithmetic proofs for later.
 **
 ** In particular, we're interested in proving bottom from a conjunction of
 ** theory literals.
 **
 ** For now, we assume that this can be done using a Farkas combination, and if
 ** that doesn't work for some reason, then we give up and "trust" the lemma.
 ** In the future we'll build support for more sophisticated reasoning.
 **
 ** Given this scope, our task is to...
 **   for each lemma (a set of literals)
 **   save the farkas coefficients for those literals
 **      which requires we save an ordering of the literals
 **      and a parallel ordering of farkas coefficients.
 **
 ** Farkas proofs have the following cocre structure:
 **    For a list of affine bounds: c[i] dot x >= b[i]
 **    and a list of non-negative coefficients: f[i],
 **    compute
 **
 **             sum_i{ (c[i] dot x) * f[i] }     and   sum_i{b[i]*f[i]}
 **
 **    and then verify that the left is actually < the right, a (=><=)
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__ARITH_PROOF_RECORDER_H
#define __CVC4__PROOF__ARITH_PROOF_RECORDER_H

#include <map>
#include <set>

#include "expr/node.h"
#include "theory/arith/constraint_forward.h"

namespace CVC4 {
namespace proof {

class ArithProofRecorder
{
 public:
  ArithProofRecorder();

  /**
   * @brief For a set of incompatible literal, save the Farkas coefficients
   * demonstrating their incompatibilty
   *
   * @param conflict a bunch of conjoined literals which form a conflict
   * @param farkasCoefficients a list of rational coefficients to multiple each
   *        literal by
   *
   * The orders of the two vectors must agree!
   */
  void saveFarkasCoefficients(
      Node conflict, theory::arith::RationalVectorCP farkasCoefficients);

  /**
   * @brief Determine whether some literals have a farkas proof of their
   * incompatibility
   *
   * @param conflict the literals which if conjoined, putatively imply bottom
   *
   * @return whether or not there is actually a proof for them.
   */
  bool hasFarkasCoefficients(const std::set<Node>& conflict) const;

  /**
   * @brief Get the Farkas Coefficients object
   *
   * @param conflict a bunch of literals which if conjoined, form a conflict
   * @return theory::arith::RationalVectorCP -- the farkas coefficients
   *         Node -- a conjunction of the problem literals in coefficient order
   *
   *         theory::arith::RationalVectorCPSentinel if there is no entry for
   * these lits
   */
  std::pair<Node, theory::arith::RationalVectorCP> getFarkasCoefficients(
      const std::set<Node>& conflict) const;

 protected:
  // For each lemma, save the farkas coefficients of that lemma
  std::map<std::set<Node>, std::pair<Node, theory::arith::RationalVector>>
      d_lemmasToFarkasCoefficients;
};

}  // namespace proof
}  // namespace CVC4

#endif
