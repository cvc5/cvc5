/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strings proof manager utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__PROOF_MANAGER_H
#define CVC4__THEORY__STRINGS__PROOF_MANAGER_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/uf/equality_proof_manager.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * A proof manager for strings.
 *
 * This is intended to be run in parallel with an EqualityEngine. It tracks
 * the reason for why all facts are added to an EqualityEngine in a SAT-context
 * depnendent manner.
 */
class ProofManager : public eq::EqProofManager
{
 public:
  ProofManager(context::Context* c, EqualityEngine& ee, ProofChecker* pc);
  ~ProofManager() {}
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_MANAGER_H */
