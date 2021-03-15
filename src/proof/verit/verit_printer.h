/*********************                                                        */
/*! \file verit_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing veriT proof nodes
 **/

#ifndef CVC4__PROOF__VERIT_PROOF_PRINTER_H
#define CVC4__PROOF__VERIT_PROOF_PRINTER_H

#include "cvc4_private.h"
#include "expr/proof_node.h"
#include "proof/verit/verit_proof_rule.h"
//#include "proof/verit/verit_proof_checker.h"


#include <iostream>

namespace CVC4 {

namespace proof {

class VeritProofPrinter
{
 public:
   VeritProofPrinter(bool extended);
   ~VeritProofPrinter() {}
   /**
   * This method prints a proof node that has been transformed into the veriT proof format
   *
   * @param out The stream to write to
   * @param pfn The proof node to be printed
   */
   void veritPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn);
 private:
   /** Used for printing after the initial anchor */
   std::string veritPrinterInternal(std::ostream& out, std::shared_ptr<ProofNode> pfn);
   /** Flag to indicate whether the veriT proof format should be extended */
   bool d_extended;
   /** The current level of nesting, which increases when in a subproof */
   int assumption_level;
   /** Current step id */
   int step_id;
   /** The current prefix which is updated whenever a subproof is encountered
    * E.g. prefix = "t19.t2." */
   std::string prefix;
   /** A list of assumption lists for every level of the nested proof node */
   //Note: This could easily be replaced by a map, e.g. to deal with named assumptions
   std::vector<std::vector<Node>> assumptions;
};



/**
 * This method prints a proof node that has been transformed into the veriT proof format
 *
 * @param out The stream to write to
 * @param pfn The proof node to be printed
 */
static void veritPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  VeritProofPrinter vpp(true);
  vpp.veritPrinter(out,pfn);

  /*out << "\n";
  out << "Check proof? (0/1)" << "\n";
  bool check;
  std::cin >> check;
  if (check)
  {
    veritProofChecker(pfn->getChildren()[0], out);
  }*/
}

}  // namespace proof

}  // namespace CVC4

#endif
