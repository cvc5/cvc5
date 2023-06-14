/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_CHECKER_H
#define CVC5__PROOF__PROOF_CHECKER_H

#include <map>

#include "expr/node.h"
#include "options/proof_options.h"
#include "proof/proof_rule_checker.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

namespace rewriter {
class RewriteDb;
}
/** Statistics class */
class ProofCheckerStatistics
{
 public:
  ProofCheckerStatistics(StatisticsRegistry& sr);
  /** Counts the number of checks for each kind of proof rule */
  HistogramStat<PfRule> d_ruleChecks;
  /** Total number of rule checks */
  IntStat d_totalRuleChecks;
};

/** A class for checking proofs */
class ProofChecker
{
 public:
  ProofChecker(StatisticsRegistry& sr,
               options::ProofCheckMode pcMode,
               uint32_t pclevel = 0,
               rewriter::RewriteDb* rdb = nullptr);
  ~ProofChecker() {}
  /** Reset, which clears the rule checkers */
  void reset();
  /**
   * Return the formula that is proven by proof node pn, or null if pn is not
   * well-formed. If expected is non-null, then we return null if pn does not
   * prove expected.
   *
   * @param pn The proof node to check
   * @param expected The (optional) formula that is the expected conclusion of
   * the proof node.
   * @return The conclusion of the proof node if successful or null if the
   * proof is malformed, or if no checker is available for id.
   */
  Node check(ProofNode* pn, Node expected = Node::null());
  /** Same as above, with explicit arguments
   *
   * @param id The id of the proof node to check
   * @param children The children of the proof node to check
   * @param args The arguments of the proof node to check
   * @param expected The (optional) formula that is the expected conclusion of
   * the proof node.
   * @return The conclusion of the proof node if successful or null if the
   * proof is malformed, or if no checker is available for id.
   */
  Node check(PfRule id,
             const std::vector<std::shared_ptr<ProofNode>>& children,
             const std::vector<Node>& args,
             Node expected = Node::null());
  /**
   * Same as above, without conclusions instead of proof node children. This
   * is used for debugging. In particular, this function does not throw an
   * assertion failure when a proof step is malformed and can be used without
   * constructing proof nodes.
   *
   * @param id The id of the proof node to check
   * @param children The conclusions of the children of the proof node to check
   * @param args The arguments of the proof node to check
   * @param expected The (optional) formula that is the expected conclusion of
   * the proof node.
   * @param traceTag The trace tag to print debug information to
   * @return The conclusion of the proof node if successful or null if the
   * proof is malformed, or if no checker is available for id.
   */
  Node checkDebug(PfRule id,
                  const std::vector<Node>& cchildren,
                  const std::vector<Node>& args,
                  Node expected = Node::null(),
                  const char* traceTag = "");
  /** Indicate that psc is the checker for proof rule id */
  void registerChecker(PfRule id, ProofRuleChecker* psc);
  /**
   * Indicate that id is a trusted rule with the given pedantic level, e.g.:
   *  0: (mandatory) always a failure to use the given id
   *  1: (major) failure on all (non-zero) pedantic levels
   * 10: (minor) failure only on pedantic levels >= 10.
   */
  void registerTrustedChecker(PfRule id,
                              ProofRuleChecker* psc,
                              uint32_t plevel = 10);
  /** get checker for */
  ProofRuleChecker* getCheckerFor(PfRule id);
  /** get the rewrite database */
  rewriter::RewriteDb* getRewriteDatabase();
  /**
   * Get the pedantic level for id if it has been assigned a pedantic
   * level via registerTrustedChecker above, or zero otherwise.
   */
  uint32_t getPedanticLevel(PfRule id) const;

  /**
   * Is pedantic failure? If so, we return true and write a debug message on the
   * output stream out if enableOutput is true.
   */
  bool isPedanticFailure(PfRule id,
                         std::ostream& out,
                         bool enableOutput = true) const;

 private:
  /** statistics class */
  ProofCheckerStatistics d_stats;
  /** Maps proof rules to their checker */
  std::map<PfRule, ProofRuleChecker*> d_checker;
  /** Maps proof trusted rules to their pedantic level */
  std::map<PfRule, uint32_t> d_plevel;
  /** The proof checking mode */
  options::ProofCheckMode d_pcMode;
  /** The pedantic level of this checker */
  uint32_t d_pclevel;
  /** Pointer to the rewrite database */
  rewriter::RewriteDb* d_rdb;
  /**
   * Check internal. This is used by check and checkDebug above. It writes
   * checking errors on out when enableOutput is true. We treat trusted checkers
   * (nullptr in the range of the map d_checker) as failures if
   * useTrustedChecker = false.
   */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& cchildren,
                     const std::vector<Node>& args,
                     Node expected,
                     std::stringstream& out,
                     bool useTrustedChecker,
                     bool enableOutput);
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_CHECKER_H */
