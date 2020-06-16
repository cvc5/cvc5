/*********************                                                        */
/*! \file sygus_print_callback.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
                                               const std::vector<Expr>& args)
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

    // print to stream without letification
    std::stringstream body_out;
    p->toStream(body_out, sbody, -1, false, 0);

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
