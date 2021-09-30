/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Query cache
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUERY_CACHE_H
#define CVC5__THEORY__QUANTIFIERS__QUERY_CACHE_H

#include <vector>

#include "options/options.h"
#include "theory/quantifiers/expr_miner.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 */
class QueryCache : public ExprMiner
{
 public:
  /**
   * Constructor
   */
  QueryCache(Env& env, bool checkUnsat, const Options* optr = nullptr);
  ~QueryCache() {}
  /** initialize
   *
   * This initializes this expression miner. The argument vars indicates the
   * free variables of terms that will be added to this class. The argument
   * sampler gives an (optional) pointer to a sampler, which is used to
   * sample tuples of valuations of these variables.
   */
  void initialize(const std::vector<Node>& vars,
                  SygusSampler* ss = nullptr) override;
  /**
   * Return true if sol is (un)satisfiable, where sol is a formula whose free
   * variables are contained in those used to initialize this class.
   */
  bool addTerm(Node sol, std::ostream& out) override;
  bool addTerm(Node sol);

 private:
  /** Are we checking for unsatisfiability? */
  bool d_checkUnsat;
  /** True node */
  Node d_true;
  /** Sampler, caches points that satisfy queries */
  SygusSampler d_sampler;
  /** The options for subsolver calls */
  Options d_subOptions;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__QUERY_CACHE_H */
