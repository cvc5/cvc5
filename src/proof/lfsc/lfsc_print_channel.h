/*********************                                                        */
/*! \file lfsc_print_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_PRINT_CHANNEL_H
#define CVC4__PROOF__LFSC__LFSC_PRINT_CHANNEL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"
#include "printer/let_binding.h"

namespace CVC4 {
namespace proof {

class LfscPrintChannel
{
public:
  LfscPrintChannel(){}
  virtual void printNode(TNode n) {}
  virtual void printHole() {}
  virtual void printTrust(TNode res) {}
  virtual void printOpenRule(const ProofNode* pn) {}
  virtual void printCloseRule() {}
  virtual void printProofId(uint32_t id) {}
  virtual void printAssumeId(uint32_t id) {}
};

/** Prints the proof to output stream d_out */
class LfscPrintChannelOut : public LfscPrintChannel
{
public:
  LfscPrintChannelOut(std::ostream& out);
  void printNode(TNode n) override;
  void printHole() override;
  void printTrust(TNode res) override;
  void printOpenRule(const ProofNode* pn) override;
  void printCloseRule() override;
  void printProofId(uint32_t id) override;
  void printAssumeId(uint32_t id) override;
  //------------------- helper methods
  static void printRule(std::ostream& out, const ProofNode* pn);
  static void printId(std::ostream& out, uint32_t id);
  static void printProofId(std::ostream& out, uint32_t id);
  static void printAssumeId(std::ostream& out, uint32_t id);
  //------------------- end helper methods
private:
  /** The output stream */
  std::ostream& d_out;
};

/** Computes the letification of nodes that appear in the proof */
class LfscPrintChannelLetifyNode : public LfscPrintChannel
{
public:
  LfscPrintChannelLetifyNode(LetBinding& lbind);
  void printNode(TNode n) override;
  void printTrust(TNode res) override;
private:
  /** The let binding */
  LetBinding& d_lbind;
};

}  // namespace proof
}  // namespace CVC4

#endif
