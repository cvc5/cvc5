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

static std::string kindToLeanString(Kind k)
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

static std::string nodeToLeanString(Node n)
{
  Kind k = n.getKind();
  std::string kind_string = kindToLeanString(k);
  if (k == kind::VARIABLE)
  {
    return n.toString();
  }
  std::string s;
  s.append("(");
  s.append(kind_string);
  s.append(" ");
  for (int i = 0; i < n.getNumChildren(); i++)
  {
    s.append(nodeToLeanString(n[i]));
    if (i != (int)n.getNumChildren() - 1) s.append(" ");
  }
  s.append(")");
  return s;
}

static std::string nodeToLeanTypeStringAux(Node n)
{
  Kind k = n.getKind();
  if (k == kind::VARIABLE)
  {
    return n.toString();
  }
  else if (k == kind::AND)
  {
    return nodeToLeanTypeStringAux(n[0]).append(" -> ").append(
        nodeToLeanTypeStringAux(n[1]));
  }
  else
  {
    std::string s = "holds [";
    return s.append(nodeToLeanString(n)).append("]");
  }
}

static std::string nodeToLeanTypeString(Node n)
{
  return nodeToLeanTypeStringAux(n[0]).append(" -> holds []");
}

static void leanPrinterInternal(std::ostream& out,
                                std::shared_ptr<ProofNode> pfn,
                                std::map<Node, std::string>& passumeMap)
{
  // should print preamble
  // should print sorts
  // should print terms, letified

  // should print theorem statement
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (std::shared_ptr<ProofNode> ch : children)
  {
    leanPrinterInternal(out, ch, passumeMap);
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
      int var_index = passumeMap.size();
      std::string var_string =
          ((std::string) "v").append(std::to_string(var_index));
      passumeMap[args[1]] = var_string;
      out << "(assume (" << var_string << " : holds ["
          << nodeToLeanString(args[1]) << "]),\n";
      break;
    };
    case LeanRule::SCOPE:
    {
      for (int i = 2; i < args.size(); i++)
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
  // should traverse proof node, print each as a proof step, according to the
  // LEAN_RULE id in the LeanRule enum
  // out << pfn;
}

static void leanPrinter(std::ostream& out,
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
  leanPrinterInternal(out, pfn, passumeMap);
  out << "\n";
}

}  // namespace proof
}  // namespace CVC4

#endif
