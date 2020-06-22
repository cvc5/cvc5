/*********************                                                        */
/*! \file array_proof_reconstruction.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Array-specific proof construction logic to be used during the
 ** equality engine's path reconstruction
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__ARRAY_PROOF_RECONSTRUCTION_H
#define CVC4__THEORY__ARRAYS__ARRAY_PROOF_RECONSTRUCTION_H

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

  void notify(unsigned reasonType, Node reason, Node a, Node b,
              std::vector<TNode>& equalities,
              eq::EqProof* proof) const override;

  void setRowMergeTag(unsigned tag);
  void setRow1MergeTag(unsigned tag);
  void setExtMergeTag(unsigned tag);

private:
  /** Merge tag for ROW applications */
  unsigned d_reasonRow;
  /** Merge tag for ROW1 applications */
  unsigned d_reasonRow1;
  /** Merge tag for EXT applications */
  unsigned d_reasonExt;

  const eq::EqualityEngine* d_equalityEngine;
}; /* class ArrayProofReconstruction */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARRAYS__ARRAY_PROOF_RECONSTRUCTION_H */
