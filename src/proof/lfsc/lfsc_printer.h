/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"

namespace cvc5::internal {
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
class LfscPrinter : protected EnvObj
{
 public:
  LfscPrinter(Env& env, LfscNodeConverter& ltp, rewriter::RewriteDb* rdb);
  ~LfscPrinter() {}

  /**
   * Print the full proof of false by pn on output stream out.
   */
  void print(std::ostream& out, const ProofNode* pn);

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
   * This ensures that the type definition of type tn has been
   * printed, which ensures that all of its component types, and the
   * user-defined subfields of datatype types among those are declared. This
   * furthermore includes running to a fixed point in the case that tn contains
   * subfield types that are themselves datatypes.
   * Notice that type definitions do not include printing the symbols of the
   * datatype.
   *
   * @param os The stream to print to
   * @param tn The type to ensure the definition(s) are printed for
   * @param processed The types whose definitions we have already printed
   * @param tupleArityProcessed The arity of tuples that we have declared.
   * Note this is only required until we have a more robust treatment of
   * tuples in the LFSC signature
   */
  void ensureTypeDefinitionPrinted(
      std::ostream& os,
      TypeNode tn,
      std::unordered_set<TypeNode>& processed,
      std::unordered_set<size_t>& tupleArityProcessed);
  /**
   * print type definition, which is the same as above, but does not process
   * component types.
   */
  void printTypeDefinition(std::ostream& os,
                           TypeNode tn,
                           std::unordered_set<TypeNode>& processed,
                           std::unordered_set<size_t>& tupleArityProcessed);
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
   * parentheses on cparen. If asDefs is true, then the definition is printed
   * as a standalone define statement on out.
   */
  void printLetList(std::ostream& out,
                    std::ostream& cparen,
                    LetBinding& lbind,
                    bool asDefs = false);

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
   * Print a plet proof on output channel out, where p is the letified
   * proof and pid is its identifier for the given name prefix.
   * The remaining arguments are used for printing p.
   */
  void printPLet(LfscPrintChannel* out,
                 const ProofNode* p,
                 size_t pid,
                 const std::string& prefix,
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
  /** Counter for plet definitions for children of trust steps */
  size_t d_trustChildPletCounter;
  /** term prefix */
  std::string d_termLetPrefix;
  /** assumption prefix */
  std::string d_assumpPrefix;
  /** proof letified prefix */
  std::string d_pletPrefix;
  /** proof letified trust child prefix */
  std::string d_pletTrustChildPrefix;
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
}  // namespace cvc5::internal

#endif
