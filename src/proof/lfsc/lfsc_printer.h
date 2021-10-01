/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The printer for LFSC proofs
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_PRINTER_H
#define CVC4__PROOF__LFSC__LFSC_PRINTER_H

#include <iosfwd>
#include <map>

#include "expr/node.h"
#include "printer/let_binding.h"
#include "proof/lfsc/lfsc_node_converter.h"
#include "proof/lfsc/lfsc_util.h"
#include "proof/print_expr.h"
#include "proof/proof_node.h"
#include "rewriter/rewrite_db.h"

namespace cvc5 {
namespace proof {

class LfscPrintChannel;

/**
 * The LFSC printer, which prints proof nodes in a proof that is checkable
 * by LFSC using the signature, currently located at:
 * https://github.com/CVC4/signatures/tree/master/lfsc/new.
 *
 * It expects to print proof nodes that have been processed by the LFSC
 * proof post processor.
 */
class LfscPrinter
{
 public:
  LfscPrinter(LfscNodeConverter& ltp, rewriter::RewriteDb* rdb);
  ~LfscPrinter() {}

  /**
   * Print the full proof of assertions => false by pn on output stream out.
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
   * Print node to stream in the expected format of LFSC, where n has been
   * processed by the LFSC node converter.
   */
  void printInternal(std::ostream& out, Node n);
  /**
   * Print node n to stream in the expected format of LFSC, with let binding,
   * where n has been processed by the LFSC node converter.
   *
   * @param out The output stream
   * @param n The node to print
   * @param lbind The let binding to consider
   * @param letTop Whether we should consider the top-most application in n
   * for the let binding (see LetBinding::convert).
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
   * Get the arguments for the proof node application. This adds the arguments
   * of the given proof to the vector pargs.
   *
   * @return false if the proof cannot be printed in LFSC format.
   */
  bool computeProofArgs(const ProofNode* pn, std::vector<PExpr>& pargs);
  /**
   * Compute proof letification for proof node pn.
   */
  void computeProofLetification(const ProofNode* pn,
                                std::vector<const ProofNode*>& pletList,
                                std::map<const ProofNode*, size_t>& pletMap);
  /** Print DSL rule */
  void printDslRule(std::ostream& out,
                    rewriter::DslPfRule id,
                    std::vector<Node>& format);
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
  /** assumption counter */
  size_t d_assumpCounter;
  /** for debugging the open rules, the set of PfRule we have warned about */
  std::unordered_set<PfRule, PfRuleHashFunction> d_trustWarned;
  /** Pointer to the rewrite database */
  rewriter::RewriteDb* d_rdb;
  /**
   * Mapping rewrite rules to format for conditions.
   * The output of a DslRule is thus listing the term arguments, then
   * a list of ( holes | child proofs ) based on this list.
   * Each rule is mapped to a list of terms, where Node::null signifies
   * positions of holes, non-null nodes are child proofs to print.
   */
  std::map<rewriter::DslPfRule, std::vector<Node>> d_dslFormat;
};

}  // namespace proof
}  // namespace cvc5

#endif
