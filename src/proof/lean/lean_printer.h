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
#include "proof/lean/lean_rules.h"

namespace CVC3 {
namespace proof {

static uint32_t getUInt32(TNode n)
{
  return n.getConst<Rational>().getNumerator().toUnsignedInt();
}

static void leanPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // should print preamble
  // should print sorts
  // should print terms, letified

  // should print theorem statement
  out << "hello world"
      << "\n";
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  LeanRule id = static_cast<LeanRule>(getUInt32(args[0]));
  int counter = 0;
  switch (id)
  {
    case LeanRule::TRUST:
    {
      out << "trust(" << args[1] << ")";
      break;
    }
    case LeanRule::ASSUME:
    {
      out << "(assume v" << counter << " : holds [";
      for (size_t i = 1; i < args.size() - 1; i++)
      {
        out << args[i] << ", ";
      }
      out << args[args.size() - 1] << "],";
      break;
    };
    case LeanRule::SCOPE:
    {
      out << ")";
      break;
    }
  default:
    {
      out << " ? ";
      break;
    }
  }
  for (std::shared_ptr<ProofNode> ch : children)
  {
    leanPrinter(out, ch);
  }

  // should traverse proof node, print each as a proof step, according to the
  // LEAN_RULE id in the LeanRule enum
  out << pfn;
}

}  // namespace proof
}  // namespace CVC4

#endif
