/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channel for Logos proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__EO__LOGOS_PRINT_CHANNEL_H
#define CVC5__PROOF__EO__LOGOS_PRINT_CHANNEL_H

#include <iostream>
#include <map>
#include <sstream>
#include <vector>

#include "expr/node.h"
#include "proof/eo/eo_print_channel.h"

namespace cvc5::internal {
namespace proof {

/**
 * Prints the proof to output stream d_out in the form expected by Logos.
 *
 * Eunoia proof commands step, step-pop, assume, assume-pop correspond
 * one-to-one with the output of this proof channel. An example of the proof
 * output from this checker is the following:
 *
 * ...
 * def s0 : LogosState := logos_init_state
 * def s1 : LogosState := (logos_invoke_assume s0 t4)
 * def s2 : LogosState := (logos_invoke_assume s1 t7)
 * def s3 : LogosState := (logos_invoke_cmd s2
 *     (CCmd.step CRule.symm CArgList.nil
 *       (CIndexList.cons 0 CIndexList.nil)))
 * def s4 : LogosState := (logos_invoke_cmd s3
 *     (CCmd.step CRule.contra CArgList.nil
 *       (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
 * #eval! (logos_state_is_refutation s4)
 *
 * Note that premise ids refer to the relative distance of the premise from the
 * top of the stack, where 0 refers to the last formula proven, and so on.
 */
class CpcLogosChannelOut : public EoPrintChannelOut
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
  /** Lean is not able to parse Eunoia declarations, so we do not print them */
  bool printsDeclarations() const override { return false; }
  /** print term let, in Lean syntax */
  void printTermLet(const LetBinding& lbind, TNode n) override;
  /**
   * Dump the accumulated output to the output stream. This must be called
   * after the proof has been printed to this channel.
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
