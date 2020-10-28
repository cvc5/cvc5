/*********************                                                        */
/*! \file lfsc_printer.h
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

#ifndef CVC4__PROOF__LFSC__LFSC_PRINTER_H
#define CVC4__PROOF__LFSC__LFSC_PRINTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"
#include "proof/lfsc/lfsc_term_process.h"

namespace CVC4 {
namespace proof {

/**
 * LFSC rules
 */
enum class LfscRule : uint32_t
{
  NONE,
};

class LfscPrinter
{
 public:
  LfscPrinter();
  ~LfscPrinter() {}
  /**
   * Print the full proof of assertions => false by pn.
   */
  void print(std::ostream& out,
             const std::vector<Node>& assertions,
             const ProofNode* pn);
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void print(std::ostream& out, const ProofNode* pn);

  /**
   * Print node to stream in the expected format of LFSC.
   */
  void print(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  void print(std::ostream& out, TypeNode n);

 private:
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void printLetify(std::ostream& out, Node n);
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void printInternal(std::ostream& out,
                     Node n,
                     const std::map<Node, uint32_t>& letMap);
  /**
   * print let list, prints definitions of letList on out in order based on the
   * identifiers in letMap, and closing parentheses on cparen.
   */
  void printLetList(std::ostream& out,
                    std::ostream& cparen,
                    const std::vector<Node>& letList,
                    const std::map<Node, uint32_t>& letMap);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  void printInternal(std::ostream& out, TypeNode n);

  //------------------------------ printing proofs
  /** A term or a proof */
  class PExpr
  {
   public:
    PExpr() : d_node(), d_pnode(nullptr) {}
    PExpr(Node n) : d_node(n), d_pnode(nullptr) {}
    PExpr(const ProofNode* pn) : d_node(), d_pnode(pn) {}
    ~PExpr() {}
    Node d_node;
    const ProofNode* d_pnode;
  };
  /**
   * Print proof internal, after term lets and proofs for assumptions have
   * been computed.
   */
  void printProofLetify(std::ostream& out,
                        const ProofNode* pn,
                        std::map<Node, uint32_t>& letMap,
                        std::map<Node, uint32_t>& passumeMap);
  /**
   * Print proof internal, after all mappings have been computed.
   */
  void printProofInternal(std::ostream& out,
                          const ProofNode* pn,
                          std::map<Node, uint32_t>& letMap,
                          std::map<const ProofNode*, uint32_t>& pletMap,
                          std::map<Node, uint32_t>& passumeMap);
  /**
   * Get the arguments for the proof node application
   */
  void computeProofArgs(const ProofNode* pn, std::vector<PExpr>& pargs);
  //------------------------------ end printing proofs

  //------------------- atomic printing
  void printRule(std::ostream& out, const ProofNode*);
  void printId(std::ostream& out, uint32_t id);
  void printProofId(std::ostream& out, uint32_t id);
  void printAssumeId(std::ostream& out, uint32_t id);
  //------------------- end atomic printing

  /** The LFSC term processor callback */
  LfscTermProcessCallback d_lcb;
  /** The term processor */
  TermProcessor d_tproc;
  /** A hole */
  PExpr d_hole;
};

}  // namespace proof
}  // namespace CVC4

#endif
