/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle checker, caches oracle caller objects
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ORACLE_CHECKER_H
#define CVC5__THEORY__QUANTIFIERS__ORACLE_CHECKER_H

#include <vector>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/oracle_caller.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Oracle checker.
 *
 * This maintains callers for all oracle functions, and can be used to evaluate
 * terms that contain oracle functions. In particular, all oracle functions
 * that are applied to "value-like" arguments only are invoked and replaced
 * by their return. A term is "value-like" if it is constant (Node::isConst())
 * or a closed lambda term.
 *
 * For example, if f is an oracle function, where evaluating the oracle
 * f on 4 returns 5, and evaluating on 7 returns 10, this class acts as a
 * node converter that may transform:
 *   f(f(4)+2) ---> f(5+2) ---> f(7) ---> 10
 */
class OracleChecker : protected EnvObj, public NodeConverter
{
 public:
  OracleChecker(Env& env) : EnvObj(env) {}
  ~OracleChecker() {}

  /**
   * Check predicted io pair is consistent, generate a lemma if
   * not. This is used to check whether a definition of an oracle function
   * is consistent in the model.
   *
   * For example, calling this method with app = f(c) and val = d will
   * check whether we have evalauted the oracle associated with f on input
   * c. If not, we invoke the oracle; otherwise we retrieve its cached value.
   * If this output d' is not d, then this method adds d' = f(c) to lemmas.
   */
  bool checkConsistent(Node app, Node val, std::vector<Node>& lemmas);
  /**
   * Evaluate an oracle application. Given input f(c), where f is an oracle
   * function symbol, this returns the result of invoking the oracle associated
   * with f. This may either correspond to a cached value, or otherwise will
   * invoke the oracle.
   */
  Node evaluateApp(Node app);

  /**
   * Evaluate all oracle function applications (recursively) in n. This is an
   * alias for convert.
   */
  Node evaluate(Node n);

  /** Has oracles? Have we invoked any oracle calls */
  bool hasOracles() const;
  /** Has oracle calls for oracle function symbol f. */
  bool hasOracleCalls(Node f) const;
  /**
   * Get the cached results for oracle function symbol f. Note the vectors
   * in the range of this method are expected to have size 1.
   */
  const std::map<Node, std::vector<Node>>& getOracleCalls(Node f) const;

 private:
  /**
   * Call back to convert, which evaluates oracle function applications and
   * rewrites all other nodes.
   */
  Node postConvert(Node n) override;
  /** map of oracle interface nodes to oracle callers **/
  std::map<Node, OracleCaller> d_callers;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
