/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for initializing subsolvers (copies of SolverEngine) during
 * solving.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SMT_ENGINE_SUBSOLVER_H
#define CVC5__THEORY__SMT_ENGINE_SUBSOLVER_H

#include <memory>
#include <vector>

#include "expr/node.h"
#include "smt/solver_engine.h"

namespace cvc5::internal {
namespace theory {

/** Set of information required for setting up a subsolver */
struct SubsolverSetupInfo
{
  /** Construct the info from explicit arguments */
  SubsolverSetupInfo(const Options& opts,
                     const LogicInfo& logicInfo,
                     TypeNode sepLocType = TypeNode::null(),
                     TypeNode sepDataType = TypeNode::null());
  /** Construct the info from Env */
  SubsolverSetupInfo(const Env& env);
  /** Construct from env, but with options replaced */
  SubsolverSetupInfo(const Env& env, const Options& opts);
  /** The options of the subsolver */
  const Options& d_opts;
  /** The logic info of the subsolver */
  const LogicInfo& d_logicInfo;
  /** The separation logic location and data types */
  TypeNode d_sepLocType;
  TypeNode d_sepDataType;
};

/**
 * This function initializes the smt engine smte to check the satisfiability
 * of the argument "query". It takes the logic and options of the current
 * SMT engine in scope.
 *
 * Notice this method intentionally does not fully initialize smte. This means
 * that the options of smte can still be modified after it is returned by
 * this method.
 *
 * Notice that some aspects of subsolvers are not incoporated by this call.
 * For example, the type of separation logic heaps is not set on smte, even
 * if the current SMT engine has declared a separation logic heap.
 *
 * @param smte The smt engine pointer to initialize
 * @param info The information for setting up the subsolver
 * @param needsTimeout Whether we would like to set a timeout
 * @param timeout The timeout (in milliseconds)
 */
void initializeSubsolver(std::unique_ptr<SolverEngine>& smte,
                         const SubsolverSetupInfo& info,
                         bool needsTimeout = false,
                         unsigned long timeout = 0);

/**
 * Version that uses the options and logicInfo in an environment.
 */
void initializeSubsolver(std::unique_ptr<SolverEngine>& smte,
                         const Env& env,
                         bool needsTimeout = false,
                         unsigned long timeout = 0);

/**
 * This returns the result of checking the satisfiability of formula query.
 *
 * If necessary, smte is initialized to the SMT engine that checked its
 * satisfiability.
 */
Result checkWithSubsolver(std::unique_ptr<SolverEngine>& smte,
                          Node query,
                          const SubsolverSetupInfo& info,
                          bool needsTimeout = false,
                          unsigned long timeout = 0);

/**
 * This returns the result of checking the satisfiability of formula query.
 *
 * In contrast to above, this is used if the user of this method is not
 * concerned with the state of the SMT engine after the check.
 *
 * @param query The query to check
 * @param info The information for setting up the subsolver
 * @param needsTimeout Whether we would like to set a timeout
 * @param timeout The timeout (in milliseconds)
 */
Result checkWithSubsolver(Node query,
                          const SubsolverSetupInfo& info,
                          bool needsTimeout = false,
                          unsigned long timeout = 0);

/**
 * This returns the result of checking the satisfiability of formula query.
 * Additionally, if the query is satisfiable, it adds the model values for vars
 * into modelVars.
 *
 * @param query The query to check
 * @param vars The variables we are interesting in getting a model for.
 * @param modelVals A vector storing the model values of variables in vars.
 * @param info The information for setting up the subsolver
 * @param needsTimeout Whether we would like to set a timeout
 * @param timeout The timeout (in milliseconds)
 */
Result checkWithSubsolver(Node query,
                          const std::vector<Node>& vars,
                          std::vector<Node>& modelVals,
                          const SubsolverSetupInfo& info,
                          bool needsTimeout = false,
                          unsigned long timeout = 0);

//--------------- utilities

/**
 * Assert formulas in core to subsolver.
 *
 * @param subsolver The subsolver to assert to
 * @param core The formulas to assert
 * @param defs The subset of core that are (recursive or ordinary) function
 * definitions. Ordinary function definitions are sent to the subsolver via
 * the defineFunction interface.
 * @param removed The subset of core that should be excluded from consideration.
 */
void assertToSubsolver(SolverEngine& subsolver,
                       const std::vector<Node>& core,
                       const std::unordered_set<Node>& defs,
                       const std::unordered_set<Node>& removed);
/**
 * Assuming smt has just been called to check-sat and returned "SAT", this
 * method adds the model for d_vars to mvs.
 */
void getModelFromSubsolver(SolverEngine& smt,
                           const std::vector<Node>& vars,
                           std::vector<Node>& mvs);

/**
 * Assuming smt has just been called to check-sat and returned "UNSAT", this
 * method get the unsat core and adds it to uasserts.
 *
 * The assertions in the argument queryAsserts (which we are not interested
 * in tracking in the unsat core) are excluded from uasserts.
 * If one of the formulas in queryAsserts was in the unsat core, then this
 * method returns true. Otherwise, this method returns false.
 */
bool getUnsatCoreFromSubsolver(SolverEngine& smt,
                               const std::unordered_set<Node>& queryAsserts,
                               std::vector<Node>& uasserts);
/** Same as above, without query asserts */
void getUnsatCoreFromSubsolver(SolverEngine& smt, std::vector<Node>& uasserts);

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SMT_ENGINE_SUBSOLVER_H */
