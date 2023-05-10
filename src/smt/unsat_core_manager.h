/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The unsat core manager of SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__UNSAT_CORE_MANAGER_H
#define CVC5__SMT__UNSAT_CORE_MANAGER_H

#include "context/cdlist.h"
#include "expr/node.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/instantiation_list.h"

namespace cvc5::internal {

namespace smt {

class Assertions;

/**
 * This class is responsible for managing the proof output of SolverEngine, as
 * well as setting up the global proof checker and proof node manager.
 */
class UnsatCoreManager : protected EnvObj
{
 public:
  UnsatCoreManager(Env& env);
  ~UnsatCoreManager(){};

  /** Gets the unsat core.
   *
   * The unsat core is the intersection of the assertions in as and the free
   * assumptions of the underlying refutation proof of pfn. Note that pfn must
   * be a "final proof", which means that it's a proof of false under a scope
   * containing all assertions.
   *
   * The unsat core is stored in the core argument.
   *
   * @param isInternal Whether this call was made internally (not by the user).
   * This impacts whether the unsat core is post-processed.
   */
  void getUnsatCore(std::shared_ptr<ProofNode> pfn,
                    const Assertions& as,
                    std::vector<Node>& core,
                    bool isInternal);

  /** Gets the relevant instaniations and skolemizations for the refutation.
   *
   * The relevant instantiations are all the conclusions of proof nodes of type
   * INSTANTIATE that occur in pfn.
   *
   * This method populates the insts map from quantified formulas occurring as
   * premises of INSTANTIATE proof nodes to its instantiations, which are a
   * matrix with each row corresponding to the terms with which the respective
   * quantified formula is instiated.
   *
   * Similiarly, for SKOLEMIZE, it populates the mapping sks will all
   * skolemization steps in the proof.
   */
  void getRelevantQuantTermVectors(std::shared_ptr<ProofNode> pfn,
                                   std::map<Node, InstantiationList>& insts,
                                   std::map<Node, std::vector<Node>>& sks,
                                   bool getDebugInfo = false);

 private:
  /**
   * Reduce an unsatisfiable core to make it minimal.
   */
  std::vector<Node> reduceUnsatCore(const Assertions& as,
                                    const std::vector<Node>& core);
}; /* class UnsatCoreManager */

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__UNSAT_CORE_MANAGER_H */
