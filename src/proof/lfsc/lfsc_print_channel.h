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
 * Print channels for LFSC proofs.
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_PRINT_CHANNEL_H
#define CVC4__PROOF__LFSC__LFSC_PRINT_CHANNEL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "printer/let_binding.h"
#include "proof/lfsc/lfsc_util.h"
#include "proof/proof_node.h"
#include "rewriter/rewrite_proof_rule.h"

namespace cvc5::internal {
namespace proof {

/**
 * LFSC proofs are printed in two phases: the first phase computes the
 * letification of terms in the proof as well as other information that is
 * required for printing the preamble of the proof. The second phase prints the
 * proof to an output stream. This is the base class for these two phases.
 */
class LfscPrintChannel
{
 public:
  LfscPrintChannel() {}
  virtual ~LfscPrintChannel() {}
  /** Print node n */
  virtual void printNode(TNode n) {}
  /** Print type node n */
  virtual void printTypeNode(TypeNode tn) {}
  /** Print a hole */
  virtual void printHole() {}
  /**
   * Print an application of the trusting the result res, whose source is the
   * given proof rule.
   */
  virtual void printTrust(TNode res, PfRule src) {}
  /** Print the opening of the rule of proof rule pn, e.g. "(and_elim ". */
  virtual void printOpenRule(const ProofNode* pn) {}
  /** Print the opening of LFSC rule lr, e.g. "(cong " */
  virtual void printOpenLfscRule(LfscRule lr) {}
  /** Print the closing of # nparen proof rules */
  virtual void printCloseRule(size_t nparen = 1) {}
  /** Print an identifier for the given prefix */
  virtual void printId(size_t id, const std::string& prefix) {}
  /** Print an end line */
  virtual void printEndLine() {}
};

/** Prints the proof to output stream d_out */
class LfscPrintChannelOut : public LfscPrintChannel
{
 public:
  LfscPrintChannelOut(std::ostream& out);
  void printNode(TNode n) override;
  void printTypeNode(TypeNode tn) override;
  void printHole() override;
  void printTrust(TNode res, PfRule src) override;
  void printOpenRule(const ProofNode* pn) override;
  void printOpenLfscRule(LfscRule lr) override;
  void printCloseRule(size_t nparen = 1) override;
  void printId(size_t id, const std::string& prefix) override;
  void printEndLine() override;
  //------------------- helper methods
  /**
   * Print node to stream in the expected format of LFSC.
   */
  static void printNodeInternal(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  static void printTypeNodeInternal(std::ostream& out, TypeNode tn);
  static void printRule(std::ostream& out, const ProofNode* pn);
  static void printId(std::ostream& out, size_t id, const std::string& prefix);
  static void printDslProofRuleId(std::ostream& out, rewriter::DslPfRule id);
  //------------------- end helper methods
 private:
  /**
   * Replaces "(_ " with "(" to eliminate indexed symbols
   * Replaces "__LFSC_TMP" with ""
   */
  static void cleanSymbols(std::string& s);
  /** The output stream */
  std::ostream& d_out;
};

/**
 * Run on the proof before it is printed, and does two preparation steps:
 * - Computes the letification of nodes that appear in the proof.
 * - Computes the set of DSL rules that appear in the proof.
 */
class LfscPrintChannelPre : public LfscPrintChannel
{
 public:
  LfscPrintChannelPre(LetBinding& lbind);
  void printNode(TNode n) override;
  void printTrust(TNode res, PfRule src) override;
  void printOpenRule(const ProofNode* pn) override;

  /** Get the DSL rewrites */
  const std::unordered_set<rewriter::DslPfRule>& getDslRewrites() const;

 private:
  /** The let binding */
  LetBinding& d_lbind;
  /** The DSL rules we have seen */
  std::unordered_set<rewriter::DslPfRule> d_dprs;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
