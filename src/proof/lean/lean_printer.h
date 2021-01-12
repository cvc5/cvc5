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
#include "expr/proof_checker.h"
#include "proof/lean/lean_rules.h"

namespace CVC4 {
namespace proof {

  //static uint32_t getUInt32(TNode n)
  //{
  //  return n.getConst<Rational>().getNumerator().toUnsignedInt();
  //  }

bool getLeanRule(Node n, LeanRule& lr)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    lr = static_cast<LeanRule>(id);
    return true;
  }
  return false;
}

LeanRule getLeanRule(Node n)
{
  LeanRule lr = LeanRule::UNKNOWN;
  getLeanRule(n, lr);
  return lr;
}

const char* toString(LeanRule id)
{
  switch (id)
  {
    case LeanRule::R0: return "R0";
    case LeanRule::R1: return "R1";
    case LeanRule::SMTCONG: return "SMTCONG";
    case LeanRule::SMTREFL: return "SMTREFL";
    case LeanRule::SMTSYMM: return "SMTSYMM";
    case LeanRule::SMTSYMM_NEG: return "SMTSYMM_NEG";
    case LeanRule::TRUST: return "TRUST";
    case LeanRule::ASSUME: return "ASSUME";
    case LeanRule::SCOPE: return "SCOPE";
    case LeanRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}
std::ostream& operator<<(std::ostream& out, LeanRule id)
{
  out << toString(id);
  return out;
}



  static void leanPrinterInternal(std::ostream& out, std::shared_ptr<ProofNode> pfn, int counter)
{
  // should print preamble
  // should print sorts
  // should print terms, letified

  // should print theorem statement
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (std::shared_ptr<ProofNode> ch : children)
    {
      leanPrinterInternal(out, ch, counter + 1);
    }
  //Trace("Hello") << args[0];
  LeanRule id = getLeanRule(args[0]);
  //Trace("Hello") << id << "\n\n";
  //LeanRule id = static_cast<LeanRule>(getUInt32(args[0]));
  //int assume_counter = 0;
  switch (id)
  {
    case LeanRule::TRUST:
    {
      //out << "trust(" << args[1] << ")";
      out << "trust\n";
      break;
    }
    case LeanRule::ASSUME:
    {
      //out << "(assume v" << counter << " : holds [";
      //for (size_t i = 1; i < args.size() - 1; i++)
      //{
      //  out << args[i] << ", ";
      //}
      //out << args[args.size() - 1] << "],";
      //break;
      out << "assume\n";
      out << "(assume l" << counter << " : holds " << args[1] << ",\n";
      break;
    };
    case LeanRule::SCOPE:
    {
      out << "scope\n";
      out << args << "\n";
      break;
    }
    case LeanRule::CHAIN_RESOLUTION:
    {
      out << "chain\n";
      if (args[3].getKind() == kind::EQUAL)
        {
         out << "R0 " << "(mkEq " << args[3][0] << " " << args[3][1] << ")";
        }
      break;
    }
  default:
    {
      out << " ?\n";
      break;
    }
  }
    // should traverse proof node, print each as a proof step, according to the
  // LEAN_RULE id in the LeanRule enum
  //out << pfn;
}

static void leanPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  const std::vector<Node>& args = pfn->getArguments();
  out << "open smt\n";
  out << "open smt.sort smt.term\n";
  out << "def s := boolsort\n";
  out << "def t := const 1 s\n";
  out << "noncomputable theorem th0 : " << args[1];
  // how to print type?
  out << ":=";
  leanPrinterInternal(out, pfn, 0);
}

}  // namespace proof
}  // namespace CVC4

#endif
