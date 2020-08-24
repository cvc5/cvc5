/*********************                                                        */
/*! \file arith_proof_recorder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class for recording the skeletons of arithmetic proofs at solve
 ** time so they can later be used during proof-production time.
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
 **   save the Farkas coefficients for those literals
 **      which requires we save an ordering of the literals
 **      and a parallel ordering of Farkas coefficients.
 **
 ** Farkas proofs have the following core structure:
 **    For a list of affine bounds: c[i] dot x >= b[i]
 **      (x is a vector of variables)
 **      (c[i] is a vector of coefficients)
 **    and a list of non-negative coefficients: f[i],
 **    compute
 **
 **             sum_i{ (c[i] dot x) * f[i] }     and   sum_i{b[i]*f[i]}
 **
 **    and then verify that the left is actually < the right, a contradiction
 **
 **    To be clear: this code does not check Farkas proofs, it just stores the
 **    information needed to write them.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__ARITH_PROOF_RECORDER_H
#define CVC4__PROOF__ARITH_PROOF_RECORDER_H

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
   * @brief For a set of incompatible literals, save the Farkas coefficients
   * demonstrating their incompatibility
   *
   * @param conflict a conjunction of conflicting literals
   * @param farkasCoefficients a list of rational coefficients which the literals
   *       should be multiplied by (pairwise) to produce a contradiction.
   *
   * The orders of the two vectors must agree!
   */
  void saveFarkasCoefficients(
      Node conflict, theory::arith::RationalVectorCP farkasCoefficients);

  /**
   * @brief Determine whether some literals have a Farkas proof of their
   * incompatibility
   *
   * @param conflict a conjunction of (putatively) conflicting literals
   *
   * @return whether or not there is actually a proof for them.
   */
  bool hasFarkasCoefficients(const std::set<Node>& conflict) const;

  /**
   * @brief Get the Farkas Coefficients object
   *
   * @param conflict a conjunction of conflicting literals
   * @return theory::arith::RationalVectorCP -- the Farkas coefficients
   *         Node -- a conjunction of the problem literals in coefficient order
   *
   *         theory::arith::RationalVectorCPSentinel if there is no entry for
   * these lits
   */
  std::pair<Node, theory::arith::RationalVectorCP> getFarkasCoefficients(
      const std::set<Node>& conflict) const;

 protected:
  // For each lemma, save the Farkas coefficients of that lemma
  std::map<std::set<Node>, std::pair<Node, theory::arith::RationalVector>>
      d_lemmasToFarkasCoefficients;
};

}  // namespace proof
}  // namespace CVC4

#endif
