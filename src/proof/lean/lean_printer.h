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

const char* toString(LeanRule id);
std::ostream& operator<<(std::ostream& out, LeanRule id);
LeanRule getLeanRule(Node n);
bool getLeanRule(Node n, LeanRule& lr);

class LeanPrinter
{
 public:
  LeanPrinter();
  ~LeanPrinter() {}
  static void print(std::ostream& out,
                    const std::vector<Node>& assertions,
                    std::shared_ptr<ProofNode> pfn);

 private:
  static std::string kindToLeanString(Kind k);
  static std::string nodeToLeanString(Node n);
  static std::string nodeToLeanTypeStringAux(Node n);
  static std::string nodeToLeanTypeString(Node n);
  static void printInternal(std::ostream& out,
                            std::shared_ptr<ProofNode> pfn,
                            std::map<Node, std::string>& passumeMap);
};

}  // namespace proof
}  // namespace CVC4

#endif
