/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Smt Environment, main access to global utilities available to
 * internal code
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__ENV_H
#define CVC5__SMT__ENV_H

#include <memory>

#include "options/options.h"
#include "proof/method_id.h"
#include "theory/logic_info.h"
#include "theory/theory_id.h"
#include "util/statistics_registry.h"

namespace cvc5::context {
class Context;
class UserContext;
}  // namespace cvc5::context

namespace cvc5::internal {

class NodeManager;
class StatisticsRegistry;
class ProofNodeManager;
class Printer;
class ResourceManager;
namespace options {
enum class OutputTag;
}
using OutputTag = options::OutputTag;

namespace smt {
class PfManager;
}

namespace theory {
class Evaluator;
class Rewriter;
class TrustSubstitutionMap;
}

/**
 * The environment class.
 *
 * This class lives in the SolverEngine and contains all utilities that are
 * globally available to all internal code.
 */
class Env
{
  friend class SolverEngine;
  friend class smt::PfManager;

 public:
  /**
   * Construct an Env with the given node manager.
   */
  Env(const Options* opts);
  /** Destruct the env.  */
  ~Env();

  /* Access to members------------------------------------------------------- */
  /** Get a pointer to the Context owned by this Env. */
  context::Context* getContext();

  /** Get a pointer to the UserContext owned by this Env. */
  context::UserContext* getUserContext();

  /**
   * Get the underlying proof node manager. Note since proofs depend on option
   * initialization, this is only available after the SolverEngine that owns
   * this environment is initialized, and only non-null if proofs are enabled.
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

  /**
   * Get a pointer to the Evaluator owned by this Env. There are two variants
   * of the evaluator, one that invokes the rewriter when evaluation is not
   * applicable, and one that does not. The former evaluator is returned when
   * useRewriter is true.
   */
  theory::Evaluator* getEvaluator(bool useRewriter = false);

  /** Get a reference to the top-level substitution map */
  theory::TrustSubstitutionMap& getTopLevelSubstitutions();

  /** Get the options object (const version only) owned by this Env. */
  const Options& getOptions() const;

  /** Get the resource manager owned by this Env. */
  ResourceManager* getResourceManager() const;

  /** Get the logic information currently set. */
  const LogicInfo& getLogicInfo() const;

  /** Get a pointer to the StatisticsRegistry. */
  StatisticsRegistry& getStatisticsRegistry();

  /* Option helpers---------------------------------------------------------- */

  /**
   * Check whether the output for the given output tag is enabled. Output tags
   * are enabled via the `output` option (or `-o` on the command line).
   */
  bool isOutputOn(OutputTag tag) const;
  /**
   * Check whether the output for the given output tag (as a string) is enabled.
   * Output tags are enabled via the `output` option (or `-o` on the command
   * line).
   */
  bool isOutputOn(const std::string& tag) const;

  /**
   * Return the output stream for the given output tag (as a string). If the
   * output tag is enabled, this returns the output stream from the `out`
   * option. Otherwise, a null stream (`cvc5::internal::null_os`) is returned.
   */
  std::ostream& output(const std::string& tag) const;

  /**
   * Return the output stream for the given output tag. If the output tag is
   * enabled, this returns the output stream from the `out` option. Otherwise,
   * a null stream (`cvc5::internal::null_os`) is returned. The user of this method needs
   * to make sure that a proper S-expression is printed.
   */
  std::ostream& output(OutputTag tag) const;

  /**
   * Check whether the verbose output for the given verbosity level is enabled.
   * The verbosity level is raised (or lowered) with the `-v` (or `-q`) option.
   */
  bool isVerboseOn(int64_t level) const;

  /**
   * Return the output stream for the given verbosity level. If the verbosity
   * level is enabled, this returns the output stream from the `err` option.
   * Otherwise, a null stream (`cvc5::internal::null_os`) is returned.
   */
  std::ostream& verbose(int64_t level) const;

  /** Convenience wrapper for verbose(0). */
  std::ostream& warning() const;

  /* Rewrite helpers--------------------------------------------------------- */
  /**
   * Evaluate node n under the substitution args -> vals. For details, see
   * theory/evaluator.h.
   *
   * @param n The node to evaluate
   * @param args The domain of the substitution
   * @param vals The range of the substitution
   * @param useRewriter if true, we use this rewriter to rewrite subterms of
   * n that cannot be evaluated to a constant.
   * @return the rewritten, evaluated form of n under the given substitution.
   */
  Node evaluate(TNode n,
                const std::vector<Node>& args,
                const std::vector<Node>& vals,
                bool useRewriter) const;
  /** Same as above, with a visited cache. */
  Node evaluate(TNode n,
                const std::vector<Node>& args,
                const std::vector<Node>& vals,
                const std::unordered_map<Node, Node>& visited,
                bool useRewriter = true) const;
  /**
   * Apply rewrite on n via the rewrite method identifier idr (see method_id.h).
   * This encapsulates the exact behavior of a REWRITE step in a proof.
   *
   * @param n The node to rewrite,
   * @param idr The method identifier of the rewriter, by default RW_REWRITE
   * specifying a call to rewrite.
   * @return The rewritten form of n.
   */
  Node rewriteViaMethod(TNode n, MethodId idr = MethodId::RW_REWRITE);

  //---------------------- information about cardinality of types
  /**
   * Is the cardinality of type tn finite? This method depends on whether
   * finite model finding is enabled. If finite model finding is enabled, then
   * we assume that all uninterpreted sorts have finite cardinality.
   *
   * Notice that if finite model finding is enabled, this method returns true
   * if tn is an uninterpreted sort. It also returns true for the sort
   * (Array Int U) where U is an uninterpreted sort. This type
   * is finite if and only if U has cardinality one; for cases like this,
   * we conservatively return that tn has finite cardinality.
   *
   * This method does *not* depend on the state of the theory engine, e.g.
   * if U in the above example currently is entailed to have cardinality >1
   * based on the assertions.
   */
  bool isFiniteType(TypeNode tn) const;

  /**
   * Set the owner of the uninterpreted sort.
   */
  void setUninterpretedSortOwner(theory::TheoryId theory);

  /**
   * Get the owner of the uninterpreted sort.
   */
  theory::TheoryId getUninterpretedSortOwner() const;

  /**
   * Return the ID of the theory responsible for the given type.
   */
  theory::TheoryId theoryOf(TypeNode typeNode) const;

  /**
   * Returns the ID of the theory responsible for the given node.
   */
  theory::TheoryId theoryOf(TNode node) const;

  /**
   * Declare heap. This is used for separation logics to set the location
   * and data types. It should be called only once, and before any separation
   * logic constraints are asserted to the theory engine.
   */
  void declareSepHeap(TypeNode locT, TypeNode dataT);

  /** Have we called declareSepHeap? */
  bool hasSepHeap() const;

  /** get the separation logic location type */
  TypeNode getSepLocType() const;
  /** get the separation logic data type */
  TypeNode getSepDataType() const;

 private:
  /* Private initialization ------------------------------------------------- */

  /** Set proof node manager if it exists */
  void finishInit(ProofNodeManager* pnm);

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
   * A pointer to the proof node manager, which is non-null if proofs are
   * enabled. This is owned by the proof manager of the SolverEngine that owns
   * this environment.
   */
  ProofNodeManager* d_proofNodeManager;
  /**
   * The rewriter owned by this Env. We have a different instance
   * of the rewriter for each Env instance. This is because rewriters may
   * hold references to objects that belong to theory solvers, which are
   * specific to an SolverEngine/TheoryEngine instance.
   */
  std::unique_ptr<theory::Rewriter> d_rewriter;
  /** Evaluator that also invokes the rewriter */
  std::unique_ptr<theory::Evaluator> d_evalRew;
  /** Evaluator that does not invoke the rewriter */
  std::unique_ptr<theory::Evaluator> d_eval;
  /** The top level substitutions */
  std::unique_ptr<theory::TrustSubstitutionMap> d_topLevelSubs;
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
   * provided as input to the SolverEngine that owns this environment. Note
   * that d_options may be modified by the options manager, e.g. based
   * on the input logic.
   *
   * This is the authorative copy of the options that internal subsolvers should
   * consider during solving and initialization.
   */
  Options d_options;
  /** Manager for limiting time and abstract resource usage. */
  std::unique_ptr<ResourceManager> d_resourceManager;
  /** The theory that owns the uninterpreted sort. */
  theory::TheoryId d_uninterpretedSortOwner;
  /** The separation logic location and data types */
  TypeNode d_sepLocType;
  TypeNode d_sepDataType;
}; /* class Env */

}  // namespace cvc5::internal

#endif /* CVC5__SMT__ENV_H */
