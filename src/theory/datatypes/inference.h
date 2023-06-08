/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datatypes inference.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__INFERENCE_H
#define CVC5__THEORY__DATATYPES__INFERENCE_H

#include "expr/node.h"
#include "proof/trust_node.h"
#include "theory/inference_id.h"
#include "theory/theory_inference.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {

class InferenceManager;

/**
 * A custom inference class. The main feature of this class is that it
 * dynamically decides whether to process itself as a fact or as a lemma,
 * based on the mustCommunicateFact method below.
 */
class DatatypesInference : public SimpleTheoryInternalFact
{
 public:
  DatatypesInference(InferenceManager* im,
                     Node conc,
                     Node exp,
                     InferenceId i = InferenceId::UNKNOWN);
  /**
   * Must communicate fact method.
   * The datatypes decision procedure makes "internal" inferences :
   *  (1) Unification : C( t1...tn ) = C( s1...sn ) => ti = si
   *  (2) Label : ~is_C1(t) ... ~is_C{i-1}(t) ~is_C{i+1}(t) ... ~is_Cn(t) =>
   * is_Ci( t )
   *  (3) Instantiate : is_C( t ) => t = C( sel_1( t ) ... sel_n( t ) )
   *  (4) collapse selector : S( C( t1...tn ) ) = t'
   *  (5) collapse term size : size( C( t1...tn ) ) = 1 + size( t1 ) + ... +
   * size( tn )
   *  (6) non-negative size : 0 <= size(t)
   * This method returns true if the fact must be sent out as a lemma. If it
   * returns false, then we assert the fact internally. We return true for (6)
   * and OR conclusions. We also return true if the option dtInferAsLemmas is
   * set to true.
   */
  static bool mustCommunicateFact(Node n, Node exp);
  /** Process lemma */
  TrustNode processLemma(LemmaProperty& p) override;
  /** Process internal fact */
  Node processFact(std::vector<Node>& exp, ProofGenerator*& pg) override;

 private:
  /** Pointer to the inference manager */
  InferenceManager* d_im;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif
