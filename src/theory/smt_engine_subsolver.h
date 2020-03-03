/*********************                                                        */
/*! \file smt_engine_subsolver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for initializing subsolvers (copies of SmtEngine) during
 ** solving.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SMT_ENGINE_SUBSOLVER_H
#define CVC4__THEORY__SMT_ENGINE_SUBSOLVER_H

#include <map>
#include <memory>
#include <vector>
#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/variable_type_map.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace theory {

/**
 * This function initializes the smt engine smte as a subsolver, e.g. it
 * creates a new SMT engine and sets the options of the current SMT engine.
 */
void initializeSubsolver(std::unique_ptr<SmtEngine>& smte);

/**
 * Initialize Smt subsolver with exporting
 *
 * This function initializes the smt engine smte to check the satisfiability
 * of the argument "query".
 *
 * The arguments em and varMap are used for supporting cases where we
 * want smte to use a different expression manager instead of the current
 * expression manager. The motivation for this so that different options can
 * be set for the subcall.
 *
 * Notice that subsequent expressions extracted from smte (for instance, model
 * values) must be exported to the current expression
 * manager.
 *
 * @param smte The smt engine pointer to initialize
 * @param em Reference to the expression manager to use
 * @param varMap Map used for exporting expressions
 * @param query The query to check
 * @param needsTimeout Whether we would like to set a timeout
 * @param timeout The timeout (in milliseconds)
 */
void initializeSubsolverWithExport(std::unique_ptr<SmtEngine>& smte,
                                   ExprManager& em,
                                   ExprManagerMapCollection& varMap,
                                   Node query,
                                   bool needsTimeout = false,
                                   unsigned long timeout = 0);

/**
 * This function initializes the smt engine smte to check the satisfiability
 * of the argument "query", without exporting expressions.
 *
 * Notice that is not possible to set a timeout value currently without
 * exporting since the Options and ExprManager are tied together.
 * TODO: eliminate this dependency (cvc4-projects #120).
 */
void initializeSubsolver(std::unique_ptr<SmtEngine>& smte, Node query);

/**
 * This returns the result of checking the satisfiability of formula query.
 *
 * If necessary, smte is initialized to the SMT engine that checked its
 * satisfiability.
 */
Result checkWithSubsolver(std::unique_ptr<SmtEngine>& smte, Node query);

/**
 * This returns the result of checking the satisfiability of formula query.
 *
 * In contrast to above, this is used if the user of this method is not
 * concerned with the state of the SMT engine after the check.
 *
 * @param query The query to check
 * @param needsTimeout Whether we would like to set a timeout
 * @param timeout The timeout (in milliseconds)
 */
Result checkWithSubsolver(Node query,
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
 * @param needsTimeout Whether we would like to set a timeout
 * @param timeout The timeout (in milliseconds)
 */
Result checkWithSubsolver(Node query,
                          const std::vector<Node>& vars,
                          std::vector<Node>& modelVals,
                          bool needsTimeout = false,
                          unsigned long timeout = 0);

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SMT_ENGINE_SUBSOLVER_H */
