/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof set utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_SET_H
#define CVC5__PROOF__PROOF_SET_H

#include <memory>

#include "context/cdlist.h"
#include "context/context.h"

namespace cvc5::internal {

class Env;

/**
 * A (context-dependent) set of proofs, which is used for memory
 * management purposes.
 */
template <typename T>
class CDProofSet
{
 public:
  CDProofSet(Env& env, context::Context* c, std::string namePrefix = "Proof")
      : d_env(env), d_proofs(c), d_namePrefix(namePrefix)
  {
  }
  /**
   * Allocate a new proof.
   *
   * This returns a fresh proof object that remains alive in the context given
   * to this class. Internally, this adds a new proof of type T to a
   * context-dependent list of proofs and passes the following arguments to the
   * T constructor:
   *   pnm, args..., name
   * where pnm is the proof node manager
   * provided to this proof set upon construction, args... are the arguments to
   * allocateProof() and name is the namePrefix with an appended index.
   */
  template <typename... Args>
  T* allocateProof(Args&&... args)
  {
    d_proofs.push_back(std::make_shared<T>(
        d_env,
        std::forward<Args>(args)...,
        d_namePrefix + "_" + std::to_string(d_proofs.size())));
    return d_proofs.back().get();
  }

 protected:
  /** Reference to env */
  Env& d_env;
  /** A context-dependent list of lazy proofs. */
  context::CDList<std::shared_ptr<T>> d_proofs;
  /** The name prefix of the lazy proofs */
  std::string d_namePrefix;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__LAZY_PROOF_SET_H */
