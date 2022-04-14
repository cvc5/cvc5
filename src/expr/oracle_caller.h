/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "expr/node_trie.h"

namespace cvc5::internal {

/**
 * This class manages the calls to an (external) binary for a single oracle
 * function symbol or oracle interface quantified formula.
 */
class OracleCaller
{
 public:
  /**
   * @param oracleInterfaceNode The oracle function symbol or oracle interface
   * quantified formula.
   */
  OracleCaller(const Node& oracleInterfaceNode);

  ~OracleCaller() {}

  /**
   * Call an oracle with a set of arguments given as children of the application
   * fapp. Store in result res.
   *
   * Return true if the call was made, and false if it was already cached.
   *
   * If this method returns true, then runResult is set to the result returned
   * from executing the binary.
   */
  bool callOracle(const Node& fapp, Node& res, int& runResult);

  /** Get the binary name for this oracle caller */
  std::string getBinaryName() const;

  /** Get cached results for this oracle caller */
  const std::map<Node, Node>& getCachedResults() const;

  /**
   * Get binary from an oracle function, or an oracle interface quantified
   * formula.
   */
  static std::string getBinaryNameFor(const Node& n);

  /** is f an oracle function? */
  static bool isOracleFunction(Node f);
  /** is n an oracle function application? */
  static bool isOracleFunctionApp(Node n);

 private:
  /** name of binary */
  std::string d_binaryName;
  /**
   * The cached results, mapping (APPLY_UF) applications of the oracle
   * function to the parsed output of the binary.
   */
  std::map<Node, Node> d_cachedResults;
};

}  // namespace cvc5::internal

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/
