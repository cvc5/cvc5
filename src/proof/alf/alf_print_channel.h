/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channels for ALF proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALF__ALF_PRINT_CHANNEL_H
#define CVC5__PROOF__ALF__ALF_PRINT_CHANNEL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "printer/let_binding.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace proof {

/**
 * ALF proofs are printed in two phases: the first phase computes the
 * letification of terms in the proof as well as other information that is
 * required for printing the preamble of the proof. The second phase prints the
 * proof to an output stream. This is the base class for these two phases.
 */
class AlfPrintChannel
{
 public:
  AlfPrintChannel();
  virtual ~AlfPrintChannel();
  /** Print node n */
  virtual void printNode(TNode n) = 0;
  /** Print type node n */
  virtual void printTypeNode(TypeNode tn) = 0;
  /** Print assume */
  virtual void printAssume(TNode n, size_t i, bool isPush = false) = 0;
  /**
   * Print step
   * @param rname The rule name.
   * @param n The (optional) conclusion.
   * @param i The identifier for the step.
   * @param premises The list of identifiers of premises
   * @param args The arguments of the proof rule.
   * @param isPop Whether this is a step-pop command.
   */
  virtual void printStep(const std::string& rname,
                         TNode n,
                         size_t i,
                         const std::vector<size_t>& premises,
                         const std::vector<Node>& args,
                         bool isPop = false) = 0;
  /** Print trust step */
  virtual void printTrustStep(ProofRule r,
                              TNode n,
                              size_t i,
                              const std::vector<size_t>& premises,
                              const std::vector<Node>& args,
                              TNode conc) = 0;
};

/** Prints the proof to output stream d_out */
class AlfPrintChannelOut : public AlfPrintChannel
{
 public:
  AlfPrintChannelOut(std::ostream& out,
                     const LetBinding* lbind,
                     const std::string& tprefix,
                     bool trackWarn);
  void printNode(TNode n) override;
  void printTypeNode(TypeNode tn) override;
  void printAssume(TNode n, size_t i, bool isPush) override;
  void printStep(const std::string& rname,
                 TNode n,
                 size_t i,
                 const std::vector<size_t>& premises,
                 const std::vector<Node>& args,
                 bool isPop = false) override;
  void printTrustStep(ProofRule r,
                      TNode n,
                      size_t i,
                      const std::vector<size_t>& premises,
                      const std::vector<Node>& args,
                      TNode conc) override;

  /**
   * Print node to stream in the expected format of ALF.
   */
  void printNodeInternal(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected format of ALF.
   */
  void printTypeNodeInternal(std::ostream& out, TypeNode tn);
  std::ostream& getOStream() { return d_out; }

 private:
  /**
   * Helper for print steps. We set reqPremises to true if we require printing
   * premises even if empty.
   */
  void printStepInternal(const std::string& rname,
                         TNode n,
                         size_t i,
                         const std::vector<size_t>& premises,
                         const std::vector<Node>& args,
                         bool isPop,
                         bool reqPremises);
  /** The output stream */
  std::ostream& d_out;
  /** The let binding */
  const LetBinding* d_lbind;
  /** term prefix */
  std::string d_termLetPrefix;
  /**
   * The set of ProofRule that we have output a warning about, i.e. the rules
   * associated with trusted steps.
   */
  std::unordered_set<ProofRule> d_warnedRules;
  /** Are we tracking warned rules? */
  bool d_trackWarn;
};

/**
 * Run on the proof before it is printed, and does two preparation steps:
 * - Computes the letification of nodes that appear in the proof.
 * - Computes the set of variables that appear in the proof.
 */
class AlfPrintChannelPre : public AlfPrintChannel
{
 public:
  AlfPrintChannelPre(LetBinding* lbind);
  void printNode(TNode n) override;
  void printTypeNode(TypeNode tn) override;
  void printAssume(TNode n, size_t i, bool isPush) override;
  void printStep(const std::string& rname,
                 TNode n,
                 size_t i,
                 const std::vector<size_t>& premises,
                 const std::vector<Node>& args,
                 bool isPop = false) override;
  void printTrustStep(ProofRule r,
                      TNode n,
                      size_t i,
                      const std::vector<size_t>& premises,
                      const std::vector<Node>& args,
                      TNode conc) override;

 private:
  /** The let binding */
  LetBinding* d_lbind;
  /** For computing free variables */
  std::unordered_set<Node> d_keep;
  /** Process that we will print node n in the final proof */
  void processInternal(const Node& n);
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
