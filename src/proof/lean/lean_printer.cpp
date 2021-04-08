/*********************                                                        */
/*! \file lean_printer.cpp
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

#include "proof/lean/lean_printer.h"

#include <iostream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

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

LeanRule LeanPrinter::getLeanRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<LeanRule>(id);
  }
  return LeanRule::UNKNOWN;
}

void LeanPrinter::printKind(std::ostream& s, Kind k)
{
  switch (k)
  {
    case kind::EQUAL: s << "mkEq"; break;
    case kind::AND: s << "mkAnd"; break;
    case kind::OR: s << "mkOr"; break;
    case kind::NOT: s << "mkNot"; break;
    default: s << "mkOther";
  }
}

void LeanPrinter::printLeanString(std::ostream& s, Node n)
{
  Kind k = n.getKind();
  if (k == kind::VARIABLE)
  {
    s << n.toString();
  }
  else
  {
    s << "(";
    printKind(s, k);
    s << " ";
    for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      printLeanString(s, n[i]);
      if (i != size - 1)
      {
        s << " ";
      };
    }
    s << ")";
  }
}

void LeanPrinter::printLeanType(std::ostream& s, Node n)
{
  // convert from node to Lean Type syntax:
  // products are curried
  // types are wrapped in "holds [_]"
  Kind k = n.getKind();
  switch (k)
  {
    case kind::VARIABLE: s << n.toString(); break;
    case kind::AND:
    {
      printLeanType(s, n[0]);
      s << " -> ";
      printLeanType(s, n[1]);
      break;
    }
    default:
      s << "thHolds ";
      printLeanString(s, n);
      break;
  }
}

void LeanPrinter::printLeanTypeToBottom(std::ostream& s, Node n)
{
  // print Lean type corresponding to proof of unsatisfiability
  printLeanType(s, n[0]);
  s << " -> holds []";
}

void LeanPrinter::printProof(std::ostream& out,
                             std::shared_ptr<ProofNode> pfn,
                             std::map<Node, std::string>& passumeMap)
{
  // print rule specific lean syntax, traversing children before parents in
  // ProofNode tree
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  LeanRule id = getLeanRule(args[0]);
  if (id == LeanRule::SCOPE)
  {
    // each argument to the scope proof node corresponds to one scope
    //  to close in the Lean proof
    for (size_t i = 2, size = args.size(); i < size; ++i)
    {
      size_t varIndex = passumeMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      passumeMap[args[i]] = varString.str();

      out << "(assume (" << passumeMap[args[i]] << " : ";
      printLeanType(out, args[i]);
      out << "),\n";
    }
    for (const std::shared_ptr<ProofNode>& ch : children)
    {
      printProof(out, ch, passumeMap);
    }
    for (size_t j = 2, size = args.size(); j < size; ++j)
    {
      out << ")";
    }
  }
  else
  {
    for (const std::shared_ptr<ProofNode>& ch : children)
    {
      printProof(out, ch, passumeMap);
    }
  }
  switch (id)
  {
    case LeanRule::SCOPE: break;
    case LeanRule::TRUST:
    {
      out << "trust\n";
      break;
    }
    case LeanRule::ASSUME:
    {
      // get variable name
      break;
    };
    case LeanRule::R0:
    {
      // print variable names of clauses to be resolved against
      out << "R0 ";
      out << "(clAssume ";
      out << passumeMap[children[0]->getArguments()[1]] << ") ";
      out << "(clAssume ";
      out << passumeMap[children[1]->getArguments()[1]] << ") ";
      printLeanString(out, args[2]);
      break;
    }
    case LeanRule::R1:
    {
      // print variable names of clauses to be resolved against
      out << "R1 ";
      out << passumeMap[children[0]->getArguments()[1]] << " ";
      out << passumeMap[children[1]->getArguments()[1]] << " ";
      printLeanString(out, args[2]);
      break;
    }
    case LeanRule::SMTSYMM:
    {
      size_t varIndex = passumeMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      passumeMap[args[1]] = varString.str();
      out << "let " << passumeMap[args[1]];
      out << " := symm " << passumeMap[children[0]->getArguments()[0]];
      out << " in \n";
      break;
    }
    case LeanRule::SMTSYMM_NEG:
    {
      size_t varIndex = passumeMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      passumeMap[args[1]] = varString.str();
      out << "let " << passumeMap[args[1]];
      out << " := negSymm " << passumeMap[children[0]->getArguments()[0]];
      out << " in \n";
      // maybe add type to annotate term
      break;
    }
    default:
    {
      out << args;
      out << " ?\n";
      break;
    }
  }
}

void LeanPrinter::printSortsAndConstants(std::ostream& out,
                                         const std::vector<Node>& assertions,
                                         std::shared_ptr<ProofNode> pfn)
{
  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node, NodeHashFunction> syms;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<Node> iasserts;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
    iasserts.push_back(a);
  }
  int sortCount = 1;
  int symCount = 1;
  std::unordered_set<TypeNode, TypeNodeHashFunction> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isSort() && sts.find(st) == sts.end())
    {
      // declare a user defined sort, if that sort has not been encountered
      // before
      sts.insert(st);
      out << "def " << st << " := sort.atom " << sortCount << std::endl;
      sortCount += 1;
    }
    // declare a constant of a predefined sort
    out << "def " << s << " := const " << symCount << " " << st << std::endl;
    symCount += 1;
  }
}

void LeanPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid Lean output from a ProofNode
  std::map<Node, std::string> passumeMap;
  const std::vector<Node>& args = pfn->getArguments();
  out << "open smt\n";
  out << "open smt.sort smt.term\n";
  printSortsAndConstants(out, assertions, pfn);
  out << "noncomputable theorem th0 : ";
  printLeanTypeToBottom(out, args[1]);
  out << " := \n";
  printProof(out, pfn, passumeMap);
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5
