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
 * expr_miner
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EXPRESSION_MINER_H
#define CVC5__THEORY__QUANTIFIERS__EXPRESSION_MINER_H

#include <map>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {

class Env;
class SolverEngine;

namespace theory {
namespace quantifiers {

/** Expression miner
 *
 * This is a virtual base class for modules that "mines" certain information
 * from (enumerated) expressions. This includes:
 * - candidate rewrite rules (find-synth :rewrite)
 * - unsound rewrite rules (find-synth :rewrite_unsound)
 * - queries (find-synth :query)
 */
class ExprMiner : protected EnvObj
{
 public:
  ExprMiner(Env& env) : EnvObj(env), d_sampler(nullptr) {}
  virtual ~ExprMiner() {}
  /** initialize
   *
   * This initializes this expression miner. The argument vars indicates the
   * free variables of terms that will be added to this class. The argument
   * sampler gives an (optional) pointer to a sampler, which is used to
   * sample tuples of valuations of these variables.
   */
  virtual void initialize(const std::vector<Node>& vars,
                          SygusSampler* ss = nullptr);
  /** add term
   *
   * This registers term n with this expression miner, and adds expressions
   * found (e.g. rewrites, queries) to found.
   */
  virtual bool addTerm(Node n, std::vector<Node>& found) = 0;

 protected:
  /** the set of variables used by this class */
  std::vector<Node> d_vars;
  /**
   * The set of skolems corresponding to the above variables. These are
   * used during initializeChecker so that query (which may contain free
   * variables) is converted to a formula without free variables.
   */
  std::vector<Node> d_skolems;
  /** pointer to the sygus sampler object we are using */
  SygusSampler* d_sampler;
  /** Maps to skolems for each free variable based on d_vars/d_skolems. */
  std::map<Node, Node> d_fv_to_skolem;
  /** convert */
  Node convertToSkolem(Node n);
  /** initialize checker
   *
   * This function initializes the smt engine smte to check the satisfiability
   * of the argument "query", which is a formula whose free variables (of
   * kind BOUND_VARIABLE) are a subset of d_vars.
   */
  void initializeChecker(std::unique_ptr<SolverEngine>& checker,
                         Node query,
                         const SubsolverSetupInfo& info);
  /**
   * Run the satisfiability check on query and return the result
   * (sat/unsat/unknown).
   *
   * In contrast to the above method, this call should be used for cases where
   * the model for the query is not important.
   */
  Result doCheck(Node query, const SubsolverSetupInfo& info);
};

/** Identity expression miner */
class ExprMinerId : public ExprMiner
{
 public:
  ExprMinerId(Env& env) : ExprMiner(env) {}
  virtual ~ExprMinerId() {}
  /** Returns true and adds n to found */
  bool addTerm(Node n, std::vector<Node>& found) override;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EXPRESSION_MINER_H */
