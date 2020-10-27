/*********************                                                        */
/*! \file lazy_proof_set.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy proof set utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__LAZY_PROOF_SET_H
#define CVC4__EXPR__LAZY_PROOF_SET_H

#include <memory>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/lazy_proof.h"

namespace CVC4 {

/**
 * A (context-dependent) set of lazy proofs, which is used for memory
 * management purposes.
 */
class LazyCDProofSet
{
 public:
  LazyCDProofSet(ProofNodeManager* pnm,
                 context::Context* c = nullptr,
                 std::string namePrefix = "LazyCDProof");
  ~LazyCDProofSet() {}
  /**
   * Allocate a lazy proof. This returns a fresh lazy proof object that
   * remains alive in the context given to this class.  Internally, this adds a
   * LazyCDProof to the list d_pfs below.
   *
   * @param isCd Whether the proof is context-dependent (using the same context
   * that is provided to this class).
   */
  LazyCDProof* allocateProof(bool isCd = false);

 protected:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /**
   * The context we are using (either the one provided in the constructor or
   * d_context).
   */
  context::Context* d_contextUse;
  /** A context-dependent list of lazy proofs. */
  context::CDList<std::shared_ptr<LazyCDProof> > d_pfs;
  /** The name prefix of the lazy proofs */
  std::string d_namePrefix;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__LAZY_PROOF_SET_H */
