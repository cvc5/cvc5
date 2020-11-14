/*********************                                                        */
/*! \file inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datatypes inference
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__INFERENCE_H
#define CVC4__THEORY__DATATYPES__INFERENCE_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/inference_manager_buffered.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

enum class InferId : uint32_t
{
  NONE,
  // (= (C t1 ... tn) (C s1 .. sn)) => (= ti si)
  UNIF,
  // ((_ is Ci) t) => (= t (Ci (sel_1 t) ... (sel_n t)))
  INST,
  // (or ((_ is C1) t) V ... V ((_ is Cn) t))
  SPLIT,
  // (not ((_ is C1) t)) ^ ... [j] ... ^ (not ((_ is Cn) t)) => ((_ is Cj) t)
  LABEL_EXH,
  // (= t (Ci t1 ... tn)) => (= (sel_j t) rewrite((sel_j (Ci t1 ... tn))))
  COLLAPSE_SEL,
  // (= (Ci t1...tn) (Cj t1...tn)) => false
  CLASH_CONFLICT,
  // ((_ is Ci) t) ^ (= t (Cj t1 ... tn)) => false
  TESTER_CONFLICT,
  // ((_ is Ci) t) ^ ((_ is Cj) s) ^ (= t s) => false
  TESTER_MERGE_CONFLICT,
  // bisimilarity for codatatypes
  BISIMILAR,
  // cycle conflict for datatypes
  CYCLE,
};

/**
 * Converts an inference to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param i The inference
 * @return The name of the inference
 */
const char* toString(InferId i);

/**
 * Writes an inference name to a stream.
 *
 * @param out The stream to write to
 * @param i The inference to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, InferId i);

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
                     InferId i = InferId::NONE);
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
  /**
   * Process this fact, possibly as a fact or as a lemma, depending on the
   * above method.
   */
  bool process(TheoryInferenceManager* im, bool asLemma) override;
  /** Get the inference identifier */
  InferId getInferId() const;

 private:
  /** Pointer to the inference manager */
  InferenceManager* d_im;
  /** The inference */
  InferId d_id;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif
