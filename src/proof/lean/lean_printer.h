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

#include "expr/proof_node.h"

namespace CVC4 {
namespace proof {

enum LeanRule
{
  // in what format should I put these lean rules
  // all the lean rules
};

static void leanPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // should print preamble
  // should print sorts
  // should print terms, letified

  // should print theorem statement
  out << "hello world"
      << "\n";

  // should traverse proof node, print each as a proof step, according to the
  // LEAN_RULE id in the LeanRule enum
  out << pfn;
}

}  // namespace proof
}  // namespace CVC4

#endif
