/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channels for Eunoia proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__EO__EO_PRINT_CHANNEL_H
#define CVC5__PROOF__EO__EO_PRINT_CHANNEL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "printer/let_binding.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace proof {

/**
 * Eunoia proofs are printed in two phases: the first phase computes the
 * letification of terms in the proof as well as other information that is
 * required for printing the preamble of the proof. The second phase prints the
 * proof to an output stream. This is the base class for these two phases.
 */
class EoPrintChannel
{
 public:
  EoPrintChannel();
  virtual ~EoPrintChannel();
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
class EoPrintChannelOut : public EoPrintChannel
{
 public:
  EoPrintChannelOut(std::ostream& out,
                     const LetBinding* lbind,
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
   * Print node to stream in the expected Eunoia format.
   */
  void printNodeInternal(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected Eunoia format.
   */
  void printTypeNodeInternal(std::ostream& out, TypeNode tn);
  std::ostream& getOStream() { return d_out; }

 protected:
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
class EoPrintChannelPre : public EoPrintChannel
{
 public:
  EoPrintChannelPre(LetBinding* lbind);
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

/** 
 * Prints the proof to output stream d_out in the form expected by Logos.
 * 
 * Eunoia proof commands step, step-pop, assume, assume-pop correspond
 * one-to-one with the output of this proof channel. An example of the proof
 * output from this checker is the following:
 *
 * ...
 * def s0 : CState := logos_init_state
 * def s1 : CState := (logos_invoke_assume s0 t4)
 * def s2 : CState := (logos_invoke_assume s1 t7)
 * def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.symm CArgList.nil
 *                    (CIndexList.cons 0 CIndexList.nil)))
 * def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.contra CArgList.nil
 *                    (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
 * #eval! (logos_state_is_refutation s4)
 * 
 * Note that premise ids refer to the relative distance of the premise from the
 * top of the stack, where 0 refers to the last formula proven, and so on.
 */
class CpcLogosChannelOut : public AlfPrintChannelOut
{
 public:
  CpcLogosChannelOut(std::ostream& out, const LetBinding* lbind);
  /** print assume */
  void printAssume(TNode n, size_t i, bool isPush) override;
  /** print step */
  void printStep(const std::string& rname,
                 TNode n,
                 size_t i,
                 const std::vector<size_t>& premises,
                 const std::vector<Node>& args,
                 bool isPop = false) override;
  /** print trust step, gives an error */
  void printTrustStep(ProofRule r,
                      TNode n,
                      size_t i,
                      const std::vector<size_t>& premises,
                      const std::vector<Node>& args,
                      TNode conc) override;
  /**
   * Dump the accumulated output to d_out.
   */
  void finalize();

 private:
  /** The output state definition */
  std::stringstream d_stateDef;
  /** 
   * mapping premise ids to their distance from the top of the stack of formulas
   * we have proven, used to lookup premises in logos
   */
  std::map<size_t, size_t> d_stackId;
  /** the size of the stack of formulas we have proven */
  size_t d_stackSize;
  /** the size of the stack at the time of assume-push commands */
  std::vector<size_t> d_stackPush;
  /** an identifier for naming states */
  size_t d_stateId;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
