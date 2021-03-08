/*********************                                                        */
/*! \file lean_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LEAN_PROOF_PRINTER_H
#define CVC4__PROOF__LEAN_PROOF_PRINTER_H

#include <iostream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "proof/lean/lean_rules.h"

namespace CVC4 {

namespace proof {

/**
 * Converts a lean rule to a string.
 * @param id The lfsc rule
 * @return The name of the lfsc rule
 */
const char* toString(LeanRule id);

/**
 * Writes a lean rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The lean rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LeanRule id);

class LeanPrinter
{
 public:
  LeanPrinter();
  ~LeanPrinter() {}

  /**
   * Print the full proof of assertions => false by pfn.
   */
  static void print(std::ostream& out,
                    const std::vector<Node>& assertions,
                    std::shared_ptr<ProofNode> pfn);

 private:
  static LeanRule getLeanRule(Node n);
  static Node getId(std::shared_ptr<ProofNode> n);
  static Node getConclusion(std::shared_ptr<ProofNode> n);
  static void printKind(std::ostream& s, Kind k);
  static void printLeanString(std::ostream& s, Node n);
  /**
   * Convert from node to lean type syntax
   */
  static void printLeanType(std::ostream& s, Node n);
  /**
   * Print Lean type corresponding to proof of unsatisfiability
   */
  static void printLeanTypeToBottom(std::ostream& s, Node n);
  /**
   * Print user defined sorts and constants of those sorts
   */
  static void printSorts(std::ostream& out,
                         const std::vector<Node>& assertions,
                         std::shared_ptr<ProofNode> pfn);
  /**
   * Print rule specific lean syntax, traversing children before parents in ProofNode tree.
   */
  static void printProof(std::ostream& out,
                         std::shared_ptr<ProofNode> pfn,
                         std::map<Node, std::string>& passumeMap);
};

}  // namespace proof
}  // namespace CVC4

#endif
