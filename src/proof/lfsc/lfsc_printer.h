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

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_PRINTER_H
#define CVC4__PROOF__LFSC__LFSC_PRINTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"
#include "printer/let_binding.h"
#include "proof/lfsc/lfsc_node_converter.h"
#include "proof/lfsc/lfsc_util.h"
#include "proof/print_expr.h"

namespace cvc5 {
namespace proof {

class LfscPrintChannel;

class LfscPrinter
{
 public:
  LfscPrinter(LfscNodeConverter& ltp);
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
  void print(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  void printType(std::ostream& out, TypeNode n);

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
                     LetBinding& lbind,
                     bool letTop = true);
  /**
   * print let list, prints definitions of lbind on out in order, and closing
   * parentheses on cparen.
   */
  void printLetList(std::ostream& out, std::ostream& cparen, LetBinding& lbind);

  //------------------------------ printing proofs
  /**
   * Print proof internal, after term lets and proofs for assumptions have
   * been computed.
   */
  void printProofLetify(LfscPrintChannel* out,
                        const ProofNode* pn,
                        const LetBinding& lbind,
                        const std::vector<const ProofNode*>& pletList,
                        std::map<const ProofNode*, size_t>& pletMap,
                        std::map<Node, size_t>& passumeMap);
  /**
   * Print proof internal, after all mappings have been computed.
   */
  void printProofInternal(LfscPrintChannel* out,
                          const ProofNode* pn,
                          const LetBinding& lbind,
                          const std::map<const ProofNode*, size_t>& pletMap,
                          std::map<Node, size_t>& passumeMap);
  /**
   * Get the arguments for the proof node application
   */
  bool computeProofArgs(const ProofNode* pn, std::vector<PExpr>& pargs);
  /**
   * Compute proof letification for proof node pn.
   */
  void computeProofLetification(const ProofNode* pn,

                                std::vector<const ProofNode*>& pletList,
                                std::map<const ProofNode*, size_t>& pletMap);
  //------------------------------ end printing proofs
  /** The term processor */
  LfscNodeConverter& d_tproc;
  /** The proof traversal callback */
  LfscProofLetifyTraverseCallback d_lpltc;
  /** true and false nodes */
  Node d_tt;
  Node d_ff;
  /** Boolean type */
  TypeNode d_boolType;
  /** for debugging the open rules, the set of PfRule we have warned about */
  std::unordered_set<PfRule, PfRuleHashFunction> d_trustWarned;
};

}  // namespace proof
}  // namespace cvc5

#endif
