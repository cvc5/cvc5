/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "smt/proof_manager.h"
#include "smt/smt_solver.h"
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
  UnsatCoreManager(Env& env, SmtSolver& slv, PfManager& pfm);
  ~UnsatCoreManager(){};
  /**
   * Convert preprocessed assertions to the input formulas that imply them. In
   * detail, this converts a set of preprocessed assertions to a set of input
   * assertions based on the proof of preprocessing. It is used for unsat cores
   * and timeout cores.
   *
   * @param ppa The preprocessed assertions to convert
   * @param isInternal Used for debug printing unsat cores, i.e. when isInternal
   * is false, we print debug information.
   */
  std::vector<Node> convertPreprocessedToInput(const std::vector<Node>& ppa,
                                               bool isInternal);
  /**
   * Get the unsat core in the current context. Should be called only when in
   * UNSAT mode.
   * Calls convertPreprocessedToInput on the unsat core of the underyling prop
   * engine.
   * @param isInternal Used for debug printing unsat cores, i.e. when isInternal
   * is false, we print debug information.
   * @return the unsat core
   */
  std::vector<Node> getUnsatCore(bool isInternal);
  /**
   * Get the lemmas that are included in the unsat core. Should be called only
   * when in UNSAT mode. Gets the unsat core of lemmas as computed by the
   * underlying prop engine.
   * @param isInternal Used for debug printing, i.e. when isInternal is false,
   * we print debug information.
   * @return the unsat core of lemmas
   */
  std::vector<Node> getUnsatCoreLemmas(bool isInternal);
  /** Gets the relevant instaniations and skolemizations for the refutation.
   *
   * The relevant instantiations are all the conclusions of proof nodes of type
   * INSTANTIATE that occur in the proof returned by the prop engine.
   *
   * This method populates the insts map from quantified formulas occurring as
   * premises of INSTANTIATE proof nodes to its instantiations, which are a
   * matrix with each row corresponding to the terms with which the respective
   * quantified formula is instiated.
   *
   * Similiarly, for SKOLEMIZE, it populates the mapping sks will all
   * skolemization steps in the proof.
   */
  void getRelevantQuantTermVectors(std::map<Node, InstantiationList>& insts,
                                   std::map<Node, std::vector<Node>>& sks,
                                   bool getDebugInfo = false);

 private:
  /**
   * Gets the unsat core.
   *
   * The unsat core is the intersection of the assertions of the underlying
   * solver and the free assumptions of the refutation proof pfn. Note that pfn
   * must be a "final proof", which means that it's a proof of false under a
   * scope containing all assertions.
   *
   * The unsat core is stored in the core argument.
   *
   * @param pfn The refutation proof
   * @param core The unsat core, which is populated in this call
   * @param isInternal Whether this call was made internally (not by the user).
   * This impacts whether the unsat core is post-processed.
   */
  void getUnsatCoreInternal(std::shared_ptr<ProofNode> pfn,
                            std::vector<Node>& core,
                            bool isInternal);
  /**
   * Reduce an unsatisfiable core to make it minimal.
   */
  std::vector<Node> reduceUnsatCore(const Assertions& as,
                                    const std::vector<Node>& core);
  /**
   * Parition core into ordinary assertions and definitions. This method is
   * only used for printing output traces.
   */
  void partitionUnsatCore(const std::vector<Node>& core,
                          std::vector<Node>& coreDefs,
                          std::vector<Node>& coreAsserts);
  /** Reference to the SMT solver */
  SmtSolver& d_slv;
  /** Reference to the proof manager */
  PfManager& d_pfm;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__UNSAT_CORE_MANAGER_H */
