/*********************                                                        */
/*! \file dot_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Diego Camargos
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing dot proofs
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__DOT__DOT_PRINTER_H
#define CVC4__PROOF__DOT__DOT_PRINTER_H

#include <iostream>

#include "expr/proof_node.h"

namespace CVC4 {
namespace proof {

class DotPrinter
{
 public:
  DotPrinter();
  ~DotPrinter() {}

  /**
   * Print the full proof of assertions => false by pn using the dot format.
   * @param out the output stream
   * @param pn the root node of the proof to print
   */
  static void print(std::ostream& out, const ProofNode* pn);

 private:
  /**
   * Print the rule in the format:
   * "$RULE_ID $RULE_NAME($RULE_ARGUMENTS)" [ shape = "box"];
   * "$RULE_ID $RULE_NAME($RULE_ARGUMENTS)" -> "$RULE_ID $RULE_CONCLUSION";
   * and then for each child of the rule print
   * "$CHILD_ID $CHILD_CONCLUSION" -> "$RULE_ID $RULE_NAME($RULE_ARGUMENTS)";
   * and then recursively call the function with the child as argument.
   * @param out the output stream
   * @param pn the proof node to print
   * @param ruleID the id of the rule to print
   */
  static void printInternal(std::ostream& out,
                            const ProofNode* pn,
                            uint64_t& ruleID);

  /**
   * Return the arguments of a ProofNode
   * @param currentArguments an ostringstream that will store the arguments of
   * pn formatted as "$ARG[0], $ARG[1], ..., $ARG[N-1]"
   * @param pn a ProofNode
   */
  static void ruleArguments(std::ostringstream& currentArguments,
                            const ProofNode* pn);

  /** Replace all quotes but escaped quotes in given string
   * @param s The string to have the quotes processed.
   */
  static void cleanQuotes(std::string& s);
};

}  // namespace proof
}  // namespace CVC4

#endif