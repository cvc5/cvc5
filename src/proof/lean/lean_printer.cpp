/*********************                                                        */
/*! \file lean_printer.cpp
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

#include "proof/lean/lean_printer.h"

#include <iostream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "proof/lean/lean_rules.h"

namespace CVC4 {

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
  // convert a node to a Lean term -- must start with mk_ and take children as args
  // eg) kind::AND (kind::EQUAL a b) c --> mkAnd (mkEq a b) c
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
  }
  s << ")";
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
      s << "holds [";
      printLeanString(s, n);
      s << "]";
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
  // print rule specific lean syntax, traversing children before parents in ProofNode tree
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& ch : children)
  {
    printProof(out, ch, passumeMap);
  }
  LeanRule id = getLeanRule(args[0]);
  switch (id)
  {
    case LeanRule::TRUST:
    {
      out << "trust\n";
      break;
    }
    case LeanRule::ASSUME:
    {
      // keep track of variable names in assume statement using passumeMap
      size_t var_index = passumeMap.size();
      std::stringstream var_string;
      var_string << "v" << var_index;
      passumeMap[args[1]] = var_string.str();
      out << "(assume (" << var_string.str() << " : holds [";
      printLeanString(out, args[1]);
      out << "]),\n";
      break;
    };
    case LeanRule::SCOPE:
    {
      // each argument to the scope proof node corresponds to one scope
      //  to close in the lean proof
      for (size_t j = 2, size = args.size(); j < size; ++j)
      {
        out << ")";
      }
      break;
    }
    case LeanRule::R0:
    {
      //print variable names of clauses to be resolved against
      out << "R0 " << passumeMap[args[2]] << " ";
      out << passumeMap[children[0]->getArguments()[1]] << " ";
      //print term to resolve with
      printLeanString(out, children[1]->getArguments()[1]);
      break;
    }
    case LeanRule::R1:
    {
      //print variable names of clauses to be resolved against
      out << "R1 " << passumeMap[args[2]] << " ";
      out << passumeMap[children[0]->getArguments()[1]] << " ";
      //print term to resolve with
      printLeanString(out, children[1]->getArguments()[1]);
      break;
    }
    case LeanRule::SMTSYMM:
    {
      out << "@smtsymm";
      printLeanString(out, args[0]);
      out << " ";
      break;
    }
    case LeanRule::SMTSYMM_NEG:
    {
      out << "@smtsymm_neg";
      printLeanString(out, args[0]);
      out << " ";
      break;
    }
    default:
    {
      out << args;
      out << " ?\n";
      break;
    }
      out << ")";
  }
}

void LeanPrinter::printSorts(std::ostream& out,
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
  int sort_count = 1;
  int sym_count = 1;
  std::unordered_set<TypeNode, TypeNodeHashFunction> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isSort() && sts.find(st) == sts.end())
    {
      // declare a user defined sort, if that sort has not been encountered before
      sts.insert(st);
      out << "def " << st << " := sort.atom " << sort_count << std::endl;
      sort_count += 1;
    }
    // declare a constant of a predefined sort
    out << "def " << s << " := const " << sym_count << " " << st << std::endl;
    sym_count += 1;
  }
}

void LeanPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid lean output from a ProofNode
  std::map<Node, std::string> passumeMap;
  const std::vector<Node>& args = pfn->getArguments();
  out << "open smt\n";
  out << "open smt.sort smt.term\n";
  printSorts(out, assertions, pfn);
  out << "noncomputable theorem th0 : ";
  printLeanTypeToBottom(out, args[1]);
  out << " := \n";
  printProof(out, pfn, passumeMap);
  out << "\n";
}

}  // namespace proof
}  // namespace CVC4
