/*********************                                                        */
/*! \file sygus_print_callback.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus print callbacks
 **/

#include "printer/sygus_print_callback.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace printer {

SygusLetExpressionPrinter::SygusLetExpressionPrinter(
    Node let_body, std::vector<Node>& let_args, unsigned ninput_args)
{
}

void SygusLetExpressionConstructorPrinter::doStrReplace(
    std::string& str, const std::string& oldStr, const std::string& newStr)
{
  size_t pos = 0;
  while ((pos = str.find(oldStr, pos)) != std::string::npos)
  {
    str.replace(pos, oldStr.length(), newStr);
    pos += newStr.length();
  }
}

void SygusLetExpressionConstructorPrinter::toStreamSygus(Printer* p,
                                                         std::ostream& out,
                                                         Expr e)
{
  std::stringstream let_out;
  // print as let term
  if (d_sygus_num_let_input_args > 0)
  {
    let_out << "(let (";
  }
  std::vector<Node> subs_lvs;
  std::vector<Node> new_lvs;
  for (unsigned i = 0; i < d_sygus_let_args.size(); i++)
  {
    Node v = d_sygus_let_args[i];
    subs_lvs.push_back(v);
    std::stringstream ss;
    ss << "_l_" << new_lvs.size();
    Node lv = NodeManager::currentNM()->mkBoundVar(ss.str(), v.getType());
    new_lvs.push_back(lv);
    // map free variables to proper terms
    if (i < d_sygus_num_let_input_args)
    {
      // it should be printed as a let argument
      let_out << "(";
      let_out << lv << " " << lv.getType() << " ";
      p->toStreamSygus(let_out, e[i]);
      let_out << ")";
    }
  }
  if (d_sygus_num_let_input_args > 0)
  {
    let_out << ") ";
  }
  // print the body
  Node slet_body = d_let_body.substitute(
      subs_lvs.begin(), subs_lvs.end(), new_lvs.begin(), new_lvs.end());
  new_lvs.insert(new_lvs.end(), lvs.begin(), lvs.end());
  p->toStreamSygus(let_out, slet_body);
  if (d_sygus_num_let_input_args > 0)
  {
    let_out << ")";
  }
  // do variable substitutions since
  // ASSUMING : let_vars are interpreted literally and do not represent a class
  // of variables
  std::string lbody = let_out.str();
  for (unsigned i = 0; i < d_sygus_let_args.size(); i++)
  {
    std::stringstream old_str;
    old_str << new_lvs[i];
    std::stringstream new_str;
    if (i >= d_sygus_num_let_input_args)
    {
      p->toStreamSygus(new_str, Node::fromExpr(e[i]));
    }
    else
    {
      new_str << d_sygus_let_args[i];
    }
    doStrReplace(lbody, old_str.str().c_str(), new_str.str().c_str());
  }
  out << lbody;
}

SygusNamedConstructorPrinter::SygusNamedConstructorPrinter(std::string name)
    : d_name(name)
{
}

void SygusNamedConstructorPrinter::toStreamSygus(Printer* p,
                                                 std::ostream& out,
                                                 Expr e)
{
  if (e.getNumChildren() > 0)
  {
    out << "(";
  }
  out << d_name;
  if (e.getNumChildren() > 0)
  {
    for (unsigned i = 0; i < e.getNumChildren(); i++)
    {
      out << " ";
      p->toStreamSygus(out, e[i]);
    }
    out << ")";
  }
}

void SygusEmptyConstructorPrinter::toStreamSygus(const Printer* p,
                                                 std::ostream& out,
                                                 Expr e)
{
  if (e.getNumChildren() == 1)
  {
    p->toStreamSygus(out, e[0]);
  }
  else
  {
    Assert(false);
  }
}

} /* CVC4::printer namespace */
} /* CVC4 namespace */
