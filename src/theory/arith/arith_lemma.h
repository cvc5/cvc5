/*********************                                                        */
/*! \file arith_lemma.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ArithLemma class, derived from Lemma.
 **/

#ifndef CVC4__THEORY__ARITH__ARITH_LEMMA_H
#define CVC4__THEORY__ARITH__ARITH_LEMMA_H

#include <tuple>
#include <vector>

#include "expr/node.h"
#include "theory/arith/nl/inference.h"
#include "theory/inference_manager_buffered.h"
#include "theory/output_channel.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * The data structure for a single lemma to process by the arithmetic theory,
 * derived from theory::Lemma.
 *
 * This also includes the inference type that produced this lemma and data
 * structures that encapsulate the side effect of adding this lemma in the
 * non-linear solver. This is used to specify how the state of the non-linear
 * solver should update. This includes:
 * - A set of secant points to record (for transcendental secant plane
 * inferences).
 */
class ArithLemma : public Lemma
{
 public:
  ArithLemma(Node n,
             LemmaProperty p,
             ProofGenerator* pg,
             nl::Inference inf = nl::Inference::UNKNOWN)
      : Lemma(n, p, pg), d_inference(inf)
  {
  }
  ~ArithLemma() {}

  /** The inference id for the lemma */
  nl::Inference d_inference;

  /** secant points to add
   *
   * A member (tf, d, c) in this vector indicates that point c should be added
   * to the list of secant points for an application of a transcendental
   * function tf for Taylor degree d. This is used for incremental linearization
   * for underapproximation (resp. overapproximations) of convex (resp.
   * concave) regions of transcendental functions. For details, see
   * Cimatti et al., CADE 2017.
   */
  std::vector<std::tuple<Node, unsigned, Node> > d_secantPoint;
};
/**
 * Writes an arithmetic lemma to a stream.
 */
std::ostream& operator<<(std::ostream& out, const ArithLemma& al);

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__ARITH_LEMMA_H */
