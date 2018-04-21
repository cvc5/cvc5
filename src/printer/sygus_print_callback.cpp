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

#include "expr/node.h"
#include "printer/printer.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace printer {

SygusExprPrintCallback::SygusExprPrintCallback(Expr body,
                                               std::vector<Expr>& args)
    : d_body(body), d_body_argument(-1)
{
  d_args.insert(d_args.end(), args.begin(), args.end());
  for (unsigned i = 0, size = d_args.size(); i < size; i++)
  {
    if (d_args[i] == d_body)
    {
      d_body_argument = static_cast<int>(i);
    }
  }
}

void SygusExprPrintCallback::doStrReplace(std::string& str,
                                          const std::string& oldStr,
                                          const std::string& newStr) const
{
  size_t pos = 0;
  while ((pos = str.find(oldStr, pos)) != std::string::npos)
  {
    str.replace(pos, oldStr.length(), newStr);
    pos += newStr.length();
  }
}

void SygusExprPrintCallback::toStreamSygus(const Printer* p,
                                           std::ostream& out,
                                           Expr e) const
{
  // optimization: if body is equal to an argument, then just print that one
  if (d_body_argument >= 0)
  {
    p->toStreamSygus(out, Node::fromExpr(e[d_body_argument]));
  }
  else
  {
    // make substitution
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (unsigned i = 0, size = d_args.size(); i < size; i++)
    {
      vars.push_back(Node::fromExpr(d_args[i]));
      std::stringstream ss;
      ss << "_setpc_var_" << i;
      Node lv = NodeManager::currentNM()->mkBoundVar(
          ss.str(), TypeNode::fromType(d_args[i].getType()));
      subs.push_back(lv);
    }

    // the substituted body should be a non-sygus term
    Node sbody = Node::fromExpr(d_body);
    sbody =
        sbody.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());

    std::stringstream body_out;
    body_out << sbody;

    // do string substitution
    Assert(e.getNumChildren() == d_args.size());
    std::string str_body = body_out.str();
    for (unsigned i = 0, size = d_args.size(); i < size; i++)
    {
      std::stringstream old_str;
      old_str << subs[i];
      std::stringstream new_str;
      p->toStreamSygus(new_str, Node::fromExpr(e[i]));
      doStrReplace(str_body, old_str.str().c_str(), new_str.str().c_str());
    }
    out << str_body;
  }
}

SygusLetExprPrintCallback::SygusLetExprPrintCallback(
    Expr let_body, std::vector<Expr>& let_args, unsigned ninput_args)
    : SygusExprPrintCallback(let_body, let_args),
      d_num_let_input_args(ninput_args)
{
}

void SygusLetExprPrintCallback::toStreamSygus(const Printer* p,
                                              std::ostream& out,
                                              Expr e) const
{
  std::stringstream let_out;
  // print as let term
  if (d_num_let_input_args > 0)
  {
    let_out << "(let (";
  }
  std::vector<Node> subs_lvs;
  std::vector<Node> new_lvs;
  for (unsigned i = 0, size = d_args.size(); i < size; i++)
  {
    Node v = d_args[i];
    subs_lvs.push_back(v);
    std::stringstream ss;
    ss << "_l_" << new_lvs.size();
    Node lv = NodeManager::currentNM()->mkBoundVar(ss.str(), v.getType());
    new_lvs.push_back(lv);
    // map free variables to proper terms
    if (i < d_num_let_input_args)
    {
      // it should be printed as a let argument
      let_out << "(";
      let_out << lv << " " << lv.getType() << " ";
      p->toStreamSygus(let_out, e[i]);
      let_out << ")";
    }
  }
  if (d_num_let_input_args > 0)
  {
    let_out << ") ";
  }
  // print the body
  Node slet_body = Node::fromExpr(d_body);
  slet_body = slet_body.substitute(
      subs_lvs.begin(), subs_lvs.end(), new_lvs.begin(), new_lvs.end());
  // new_lvs.insert(new_lvs.end(), lvs.begin(), lvs.end());
  p->toStreamSygus(let_out, slet_body);
  if (d_num_let_input_args > 0)
  {
    let_out << ")";
  }
  // do variable substitutions since
  // ASSUMING : let_vars are interpreted literally and do not represent a class
  // of variables
  std::string lbody = let_out.str();
  for (unsigned i = 0, size = d_args.size(); i < size; i++)
  {
    std::stringstream old_str;
    old_str << new_lvs[i];
    std::stringstream new_str;
    if (i >= d_num_let_input_args)
    {
      p->toStreamSygus(new_str, Node::fromExpr(e[i]));
    }
    else
    {
      new_str << d_args[i];
    }
    doStrReplace(lbody, old_str.str().c_str(), new_str.str().c_str());
  }
  out << lbody;
}

SygusNamedPrintCallback::SygusNamedPrintCallback(std::string name)
    : d_name(name)
{
}

void SygusNamedPrintCallback::toStreamSygus(const Printer* p,
                                            std::ostream& out,
                                            Expr e) const
{
  if (e.getNumChildren() > 0)
  {
    out << "(";
  }
  out << d_name;
  if (e.getNumChildren() > 0)
  {
    for (Expr ec : e)
    {
      out << " ";
      p->toStreamSygus(out, ec);
    }
    out << ")";
  }
}

void SygusEmptyPrintCallback::toStreamSygus(const Printer* p,
                                            std::ostream& out,
                                            Expr e) const
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

std::shared_ptr<SygusEmptyPrintCallback> SygusEmptyPrintCallback::d_empty_pc = nullptr;

} /* CVC4::printer namespace */
} /* CVC4 namespace */
