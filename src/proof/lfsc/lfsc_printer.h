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
#include "printer/let_binding.h"
#include "proof/lfsc/lfsc_term_process.h"

namespace CVC4 {
namespace proof {

/**
work steps:
1. make new rules in the lfsc signature
2. add to LfscRule enum
3. print in toString
4. convert PfRule to LfscRule in the postprocessor
5. Add printing code to computeProofArgs
*/

/**
 * LFSC rules
 */
enum class LfscRule : uint32_t
{
  //----------- translated rules
  SYMM,
  NEG_SYMM,
  TRANS,
  CONG,
  CNF_AND_POS_1,
  CNF_AND_POS_2,
  //----------- unknown
  UNKNOWN,
};

/**
 * Converts a lfsc rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The lfsc rule
 * @return The name of the lfsc rule
 */
const char* toString(LfscRule id);

/**
 * Writes a lfsc rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The lfsc rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LfscRule id);
LfscRule getLfscRule(Node n);
bool getLfscRule(Node n, LfscRule& lr);
Node mkLfscRuleNode(LfscRule r);

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
                     LetBinding& lbind,
                     bool letTop = true);
  /**
   * print let list, prints definitions of lbind on out in order, and closing
   * parentheses on cparen.
   */
  void printLetList(std::ostream& out, std::ostream& cparen, LetBinding& lbind);
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
    /** The node */
    Node d_node;
    /** The proof node */
    const ProofNode* d_pnode;
  };
  class PExprStream
  {
   public:
    PExprStream(std::vector<PExpr>& stream) : d_stream(stream) {}
    /** Append a proof node */
    PExprStream& operator<<(const ProofNode* pn)
    {
      d_stream.push_back(PExpr(pn));
      return *this;
    }
    /** Append a node */
    PExprStream& operator<<(Node n)
    {
      d_stream.push_back(PExpr(n));
      return *this;
    }
    /** Append a pexpr */
    PExprStream& operator<<(PExpr p)
    {
      d_stream.push_back(p);
      return *this;
    }

   private:
    /** Reference to the stream */
    std::vector<PExpr>& d_stream;
  };
  /**
   * Print proof internal, after term lets and proofs for assumptions have
   * been computed.
   */
  void printProofLetify(std::ostream& out,
                        const ProofNode* pn,
                        LetBinding& lbind,
                        std::map<Node, uint32_t>& passumeMap);
  /**
   * Print proof internal, after all mappings have been computed.
   */
  void printProofInternal(std::ostream& out,
                          const ProofNode* pn,
                          LetBinding& lbind,
                          std::map<const ProofNode*, uint32_t>& pletMap,
                          std::map<Node, uint32_t>& passumeMap);
  /**
   * Get the arguments for the proof node application
   */
  bool computeProofArgs(const ProofNode* pn, std::vector<PExpr>& pargs);
  //------------------------------ end printing proofs

  //------------------- helper methods
  static void printRule(std::ostream& out, const ProofNode*);
  static void printId(std::ostream& out, uint32_t id);
  static void printProofId(std::ostream& out, uint32_t id);
  static void printAssumeId(std::ostream& out, uint32_t id);
  //------------------- end helper methods

  /** The term processor */
  LfscTermProcessor d_tproc;
};

}  // namespace proof
}  // namespace CVC4

#endif
