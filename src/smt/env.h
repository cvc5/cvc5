/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Smt Environment, main access to global utilities available to
 * internal code
 */

#include "cvc5_public.h"

#ifndef CVC5__SMT__ENV_H
#define CVC5__SMT__ENV_H

#include <memory>

#include "options/options.h"
#include "theory/logic_info.h"
#include "util/statistics_registry.h"

namespace cvc5 {

class NodeManager;
class StatisticsRegistry;
class ProofNodeManager;
class Printer;
class ResourceManager;

namespace context {
class Context;
class UserContext;
}  // namespace context

namespace smt {
class DumpManager;
}

namespace theory {
class Rewriter;
class TrustSubstitutionMap;
}

/**
 * The environment class.
 *
 * This class lives in the SmtEngine and contains all utilities that are
 * globally available to all internal code.
 */
class Env
{
  friend class SmtEngine;

 public:
  /**
   * Construct an Env with the given node manager.
   */
  Env(NodeManager* nm, const Options* opts);
  /** Destruct the env.  */
  ~Env();

  /* Access to members------------------------------------------------------- */
  /** Get a pointer to the Context owned by this Env. */
  context::Context* getContext();

  /** Get a pointer to the UserContext owned by this Env. */
  context::UserContext* getUserContext();

  /** Get a pointer to the underlying NodeManager. */
  NodeManager* getNodeManager() const;

  /**
   * Get the underlying proof node manager. Note since proofs depend on option
   * initialization, this is only available after the SmtEngine that owns this
   * environment is initialized, and only non-null if proofs are enabled.
   */
  ProofNodeManager* getProofNodeManager();

  /**
   * Check whether the SAT solver should produce proofs. Other than whether
   * the proof node manager is set, SAT proofs are only generated when the
   * unsat core mode is not ASSUMPTIONS.
   */
  bool isSatProofProducing() const;

  /**
   * Check whether theories should produce proofs as well. Other than whether
   * the proof node manager is set, theory engine proofs are conditioned on the
   * relationship between proofs and unsat cores: the unsat cores are in
   * FULL_PROOF mode, no proofs are generated on theory engine.
   */
  bool isTheoryProofProducing() const;

  /** Get a pointer to the Rewriter owned by this Env. */
  theory::Rewriter* getRewriter();

  /** Get a reference to the top-level substitution map */
  theory::TrustSubstitutionMap& getTopLevelSubstitutions();

  /** Get a pointer to the underlying dump manager. */
  smt::DumpManager* getDumpManager();

  /** Get the options object (const version only) owned by this Env. */
  const Options& getOptions() const;

  /** Get the original options object (const version only). */
  const Options& getOriginalOptions() const;

  /** Get the resource manager owned by this Env. */
  ResourceManager* getResourceManager() const;

  /** Get the logic information currently set. */
  const LogicInfo& getLogicInfo() const;

  /** Get a pointer to the StatisticsRegistry. */
  StatisticsRegistry& getStatisticsRegistry();

  /* Option helpers---------------------------------------------------------- */

  /**
   * Get the current printer based on the current options
   * @return the current printer
   */
  const Printer& getPrinter();

  /**
   * Get the output stream that --dump=X should print to
   * @return the output stream
   */
  std::ostream& getDumpOut();

 private:
  /* Private initialization ------------------------------------------------- */

  /** Set proof node manager if it exists */
  void setProofNodeManager(ProofNodeManager* pnm);

  /* Private shutdown ------------------------------------------------------- */
  /**
   * Shutdown method, which destroys the non-essential members of this class
   * in preparation for destroying SMT engine.
   */
  void shutdown();
  /* Members ---------------------------------------------------------------- */

  /** The SAT context owned by this Env */
  std::unique_ptr<context::Context> d_context;
  /** User level context owned by this Env */
  std::unique_ptr<context::UserContext> d_userContext;
  /**
   * A pointer to the node manager of this environment. A node manager is
   * not necessarily unique to an SmtEngine instance.
   */
  NodeManager* d_nodeManager;
  /**
   * A pointer to the proof node manager, which is non-null if proofs are
   * enabled. This is owned by the proof manager of the SmtEngine that owns
   * this environment.
   */
  ProofNodeManager* d_proofNodeManager;
  /**
   * The rewriter owned by this Env. We have a different instance
   * of the rewriter for each Env instance. This is because rewriters may
   * hold references to objects that belong to theory solvers, which are
   * specific to an SmtEngine/TheoryEngine instance.
   */
  std::unique_ptr<theory::Rewriter> d_rewriter;
  /** The top level substitutions */
  std::unique_ptr<theory::TrustSubstitutionMap> d_topLevelSubs;
  /** The dump manager */
  std::unique_ptr<smt::DumpManager> d_dumpManager;
  /**
   * The logic we're in. This logic may be an extension of the logic set by the
   * user, which may be different from the user-provided logic due to the
   * options we have set.
   *
   * This is the authorative copy of the logic that internal subsolvers should
   * consider during solving and initialization.
   */
  LogicInfo d_logic;
  /**
   * The statistics registry owned by this Env.
   */
  std::unique_ptr<StatisticsRegistry> d_statisticsRegistry;
  /**
   * The options object, which contains the modified version of the options
   * provided as input to the SmtEngine that owns this environment. Note
   * that d_options may be modified by the options manager, e.g. based
   * on the input logic.
   *
   * This is the authorative copy of the options that internal subsolvers should
   * consider during solving and initialization.
   */
  Options d_options;
  /**
   * A pointer to the original options object as stored in the api::Solver.
   * The referenced objects holds the options as initially parsed before being
   * changed, e.g., by setDefaults().
   */
  const Options* d_originalOptions;
  /** Manager for limiting time and abstract resource usage. */
  std::unique_ptr<ResourceManager> d_resourceManager;
}; /* class Env */

}  // namespace cvc5

#endif /* CVC5__SMT__ENV_H */
