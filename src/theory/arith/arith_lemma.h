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
#include "theory/theory_inference.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * The data structure for a single lemma to process by the arithmetic theory,
 * derived from theory::SimpleTheoryLemma.
 *
 * This also includes the inference type that produced this lemma.
 */
class ArithLemma : public SimpleTheoryLemma
{
 public:
  ArithLemma(Node n,
             LemmaProperty p,
             ProofGenerator* pg,
             nl::Inference inf = nl::Inference::UNKNOWN)
      : SimpleTheoryLemma(n, p, pg), d_inference(inf)
  {
  }
  virtual ~ArithLemma() {}

  /** The inference id for the lemma */
  nl::Inference d_inference;
};
/**
 * Writes an arithmetic lemma to a stream.
 */
std::ostream& operator<<(std::ostream& out, const ArithLemma& al);

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__ARITH_LEMMA_H */
