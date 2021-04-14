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
#include "proof/lfsc/lfsc_util.h"

namespace cvc5 {
namespace proof {

class LfscPrintChannel
{
 public:
  LfscPrintChannel() : d_nodeCount(0), d_trustCount(0) {}
  virtual ~LfscPrintChannel() {}
  virtual void printNode(TNode n) {}
  virtual void printTypeNode(TypeNode tn) {}
  virtual void printHole() {}
  virtual void printTrust(TNode res, PfRule src) {}
  virtual void printOpenRule(const ProofNode* pn) {}
  virtual void printOpenLfscRule(LfscRule lr) {}
  virtual void printCloseRule(size_t nparen = 1) {}
  virtual void printProofId(size_t id) {}
  virtual void printAssumeId(size_t id) {}
  virtual void printEndLine() {}
  /** temproary debug */
  size_t d_nodeCount;
  size_t d_trustCount;
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
  void printProofId(size_t id) override;
  void printAssumeId(size_t id) override;
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
  static void printId(std::ostream& out, size_t id);
  static void printProofId(std::ostream& out, size_t id);
  static void printAssumeId(std::ostream& out, size_t id);
  //------------------- end helper methods
 private:
  /** Replaces "(_ " with "(" to eliminate indexed symbols */
  static void cleanIndexedSymbols(std::string& s);
  /** The output stream */
  std::ostream& d_out;
};

/** Computes the letification of nodes that appear in the proof */
class LfscPrintChannelLetifyNode : public LfscPrintChannel
{
 public:
  LfscPrintChannelLetifyNode(LetBinding& lbind);
  void printNode(TNode n) override;
  void printTrust(TNode res, PfRule src) override;

 private:
  /** The let binding */
  LetBinding& d_lbind;
};

}  // namespace proof
}  // namespace cvc5

#endif
