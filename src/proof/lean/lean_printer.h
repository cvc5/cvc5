/*********************                                                        */
/*! \file lean_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN_PROOF_PRINTER_H
#define CVC4__PROOF__LEAN_PROOF_PRINTER_H

#include <iostream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

/**
 * Converts a Lean rule to a string.
 * @param id The Lean rule
 * @return The name of the Lean rule
 */
const char* toString(LeanRule id);

/**
 * Writes a Lean rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The Lean rule to write to the stream
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
  /**
   * Convert a CVC4 Node holding an id to the corresponding LeanRule
   */
  static LeanRule getLeanRule(Node n);
  /**
   * The Lean calculus represents x = y as (mkEq x y) and
   *  x ∧ y as (mkAnd x y).
   * printKind cases on the kind of node, and prints the
   *  corresponding Lean command among mkEq, mkAnd, mkOr, mkNot, etc
   */
  static void printKind(std::ostream& s, Kind k);
  /**
   * Convert a node to a Lean term -- must start with mk_ and take children as
   * args Example: kind::AND (kind::EQUAL a b) c --> mkAnd (mkEq a b) c
   */
  static void printLeanString(std::ostream& s, Node n);
  /**
   * Convert from node to Lean type syntax
   */
  static void printLeanType(std::ostream& s, Node n);
  /**
   * Print Lean type corresponding to proof of unsatisfiability.
   * This method is a wrapper around printLeanType.
   *  The full proof node will always be a proof of unsatisfiability
   *  via resolution. So the type printed to Lean will always end
   *  in "-> holds []", which acts like a proof of contradiction, or false.
   */
  static void printLeanTypeToBottom(std::ostream& s, Node n);
  /**
   * Print user defined sorts and constants of those sorts
   */
  static void printSortsAndConstants(std::ostream& out,
                                     const std::vector<Node>& assertions,
                                     std::shared_ptr<ProofNode> pfn);

  /**
   * For each proof node, the final Lean output's formatting depends on
   *  the particular proof rule. For example, a chain resolution must be
   *  converted into a series of sequential resolutions.
   * This method cases on the Lean proof rules (./lean_rules.h) and prints
   *  to the ostream& out.
   * Prints proof node children before parents, unless we encounter the
   *  SCOPE rule, in which case we print "assume" and bind a new variable.
   */
  static void printProof(std::ostream& out,
                         std::shared_ptr<ProofNode> pfn,
                         std::map<Node, std::string>& passumeMap);
};

}  // namespace proof
}  // namespace cvc5

#endif
