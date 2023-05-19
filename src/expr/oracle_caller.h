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
 * Oracle caller
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__ORACLE_CALLER_H
#define CVC5__EXPR__ORACLE_CALLER_H

#include "expr/node.h"
#include "expr/oracle.h"

namespace cvc5::internal {

/**
 * This class manages the calls to an (externally implemented) oracle for a
 * single oracle function symbol or oracle interface quantified formula.
 */
class OracleCaller
{
 public:
  /**
   * @param n The oracle function or oracle interface quantified formula.
   */
  OracleCaller(const Node& n);

  ~OracleCaller() {}

  /**
   * Call an oracle with a set of arguments given as children of the application
   * fapp. Store in result res.
   *
   * Return true if the call was made, and false if it was already cached.
   */
  bool callOracle(const Node& fapp, std::vector<Node>& res);

  /** Get cached results for this oracle caller */
  const std::map<Node, std::vector<Node>>& getCachedResults() const;

  /** is f an oracle function? */
  static bool isOracleFunction(Node f);
  /** is n an oracle function application? */
  static bool isOracleFunctionApp(Node n);

  /**
   * Get oracle from an oracle function, or an oracle interface quantified
   * formula. Returns a node of kind ORACLE if the associated oracle exists,
   * or null otherwise.
   */
  static Node getOracleFor(const Node& n);

 private:
  /** The oracle node */
  Node d_oracleNode;
  /** The oracle */
  const Oracle& d_oracle;
  /**
   * The cached results, mapping (APPLY_UF) applications of the oracle
   * function to the parsed output of the binary.
   */
  std::map<Node, std::vector<Node>> d_cachedResults;
};

}  // namespace cvc5::internal

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/
