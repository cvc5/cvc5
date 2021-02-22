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

std::string LeanPrinter::kindToLeanString(Kind k)
{
  switch (k)
  {
    case kind::EQUAL: return "mkEq";
    case kind::AND: return "mkAnd";
    case kind::OR: return "mkOr";
    case kind::NOT: return "mkNot";
    default: return "mkOther";
  }
}

std::string LeanPrinter::nodeToLeanString(Node n)
{
  Kind k = n.getKind();
  std::string kind_string = kindToLeanString(k);
  if (k == kind::VARIABLE)
  {
    return n.toString();
  }
  std::stringstream s;
  s << "(" << kind_string << " ";
  for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
  {
    s << nodeToLeanString(n[i]);
    if (i != size - 1)
    {
      s << " ";
    };
  }
  s << ")";
  return s.str();
}

std::string LeanPrinter::nodeToLeanTypeStringAux(Node n)
{
  Kind k = n.getKind();
  std::stringstream s;
  switch (k)
  {
    case kind::VARIABLE: s << n.toString(); break;
    case kind::AND:
    {
      s << nodeToLeanTypeStringAux(n[0]) << " -> "
        << nodeToLeanTypeStringAux(n[1]);
      break;
    }
    default: s << "holds [" << nodeToLeanString(n) << "]"; break;
  }
  return s.str();
}

std::string LeanPrinter::nodeToLeanTypeString(Node n)
{
  std::stringstream s;
  s << nodeToLeanTypeStringAux(n[0]) << " -> holds []";
  return s.str();
}

void LeanPrinter::printInternal(std::ostream& out,
                                std::shared_ptr<ProofNode> pfn,
                                std::map<Node, std::string>& passumeMap)
{
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& ch : children)
  {
    LeanPrinter::printInternal(out, ch, passumeMap);
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
      size_t var_index = passumeMap.size();
      std::stringstream var_string;
      var_string << "v" << var_index;
      passumeMap[args[1]] = var_string.str();
      out << "(assume (" << var_string.str() << " : holds ["
          << nodeToLeanString(args[1]) << "]),\n";
      break;
    };
    case LeanRule::SCOPE:
    {
      for (size_t j = 2, size = args.size(); j < size; ++j)
      {
        out << ")";
      }
      break;
    }
    case LeanRule::R0:
    {
      out << "R0 " << passumeMap[args[2]] << " ";
      out << passumeMap[children[0]->getArguments()[1]] << " ";
      out << nodeToLeanString(children[1]->getArguments()[1]);
      break;
    }
    case LeanRule::R1:
    {
      out << "R1 " << passumeMap[args[2]] << " ";
      out << passumeMap[children[0]->getArguments()[1]] << " ";
      out << nodeToLeanString(children[1]->getArguments()[1]);
      break;
    }
    default:
    {
      out << " ?\n";
      break;
    }
      out << ")";
  }
}

void LeanPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        std::shared_ptr<ProofNode> pfn)
{
  std::map<Node, std::string> passumeMap;
  const std::vector<Node>& args = pfn->getArguments();
  out << "open smt\n";
  out << "open smt.sort smt.term\n";
  // [1a] user declared sorts
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
      sts.insert(st);
      out << "def " << st << " := sort.atom " << sort_count << std::endl;
      sort_count += 1;
    }
    out << "def " << s << " := const " << sym_count << " " << st << std::endl;
    sym_count += 1;
  }
  out << "noncomputable theorem th0 : " << nodeToLeanTypeString(args[1])
      << " := \n";
  LeanPrinter::printInternal(out, pfn, passumeMap);
  out << "\n";
}

}  // namespace proof
}  // namespace CVC4
