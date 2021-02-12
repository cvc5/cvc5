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
#include <map>

#include "expr/node.h"
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
   */
  static void print(std::ostream& out, const ProofNode* pn);
};

}  // namespace proof
}  // namespace CVC4

#endif
