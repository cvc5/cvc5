/*********************                                                        */
/*! \file array_proof_reconstruction.h
 ** \verbatim
 **
 ** \brief Array-specific proof construction logic to be used during the
 ** equality engine's path reconstruction
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__ARRAY_PROOF_RECONSTRUCTION_H
#define __CVC4__THEORY__ARRAYS__ARRAY_PROOF_RECONSTRUCTION_H

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace arrays {

/**
 * A callback class to be invoked whenever the equality engine traverses
 * an "array-owned" edge during path reconstruction.
 */

class ArrayProofReconstruction : public eq::PathReconstructionNotify {
public:
  ArrayProofReconstruction(const eq::EqualityEngine* equalityEngine);

  void notify(eq::MergeReasonType reasonType, Node reason, Node a, Node b,
              std::vector<TNode>& equalities, eq::EqProof* proof) const;

private:
  const eq::EqualityEngine* d_equalityEngine;
}; /* class ArrayProofReconstruction */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__ARRAY_PROOF_RECONSTRUCTION_H */
