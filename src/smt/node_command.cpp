/*********************                                                        */
/*! \file node_command.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of NodeCommand functions.
 **
 ** Implementation of NodeCommand functions.
 **/

#include "smt/node_command.h"

#include "printer/printer.h"

namespace CVC4 {

/* -------------------------------------------------------------------------- */
/* class NodeCommand                                                          */
/* -------------------------------------------------------------------------- */

NodeCommand::~NodeCommand() {}

std::string NodeCommand::toString() const
{
  std::stringstream ss;
  toStream(ss);
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const NodeCommand& nc)
{
  nc.toStream(out,
              Node::setdepth::getDepth(out),
              Node::printtypes::getPrintTypes(out),
              Node::dag::getDag(out),
              Node::setlanguage::getLanguage(out));
  return out;
}

/* -------------------------------------------------------------------------- */
/* class DeclareFunctionNodeCommand                                           */
/* -------------------------------------------------------------------------- */

DeclareFunctionNodeCommand::DeclareFunctionNodeCommand(const std::string& id,
                                                       Node expr,
                                                       TypeNode type)
    : d_id(id),
      d_fun(expr),
      d_type(type),
      d_printInModel(true),
      d_printInModelSetByUser(false)
{
}

void DeclareFunctionNodeCommand::toStream(std::ostream& out,
                                          int toDepth,
                                          bool types,
                                          size_t dag,
                                          OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclareFunction(out, d_id, d_type);
}

NodeCommand* DeclareFunctionNodeCommand::clone() const
{
  return new DeclareFunctionNodeCommand(d_id, d_fun, d_type);
}

const Node& DeclareFunctionNodeCommand::getFunction() const { return d_fun; }

bool DeclareFunctionNodeCommand::getPrintInModel() const
{
  return d_printInModel;
}

bool DeclareFunctionNodeCommand::getPrintInModelSetByUser() const
{
  return d_printInModelSetByUser;
}

void DeclareFunctionNodeCommand::setPrintInModel(bool p)
{
  d_printInModel = p;
  d_printInModelSetByUser = true;
}

/* -------------------------------------------------------------------------- */
/* class DeclareTypeNodeCommand                                               */
/* -------------------------------------------------------------------------- */

DeclareTypeNodeCommand::DeclareTypeNodeCommand(const std::string& id,
                                               size_t arity,
                                               TypeNode type)
    : d_id(id), d_arity(arity), d_type(type)
{
}

void DeclareTypeNodeCommand::toStream(std::ostream& out,
                                      int toDepth,
                                      bool types,
                                      size_t dag,
                                      OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclareType(
      out, d_id, d_arity, d_type);
}

NodeCommand* DeclareTypeNodeCommand::clone() const
{
  return new DeclareTypeNodeCommand(d_id, d_arity, d_type);
}

const std::string DeclareTypeNodeCommand::getSymbol() const { return d_id; }

const TypeNode& DeclareTypeNodeCommand::getType() const { return d_type; }

/* -------------------------------------------------------------------------- */
/* class DeclareDatatypeNodeCommand                                           */
/* -------------------------------------------------------------------------- */

DeclareDatatypeNodeCommand::DeclareDatatypeNodeCommand(
    const std::vector<TypeNode>& datatypes)
    : d_datatypes(datatypes)
{
}

void DeclareDatatypeNodeCommand::toStream(std::ostream& out,
                                          int toDepth,
                                          bool types,
                                          size_t dag,
                                          OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDatatypeDeclaration(out,
                                                                d_datatypes);
}

NodeCommand* DeclareDatatypeNodeCommand::clone() const
{
  return new DeclareDatatypeNodeCommand(d_datatypes);
}

/* -------------------------------------------------------------------------- */
/* class DefineFunctionNodeCommand                                            */
/* -------------------------------------------------------------------------- */

DefineFunctionNodeCommand::DefineFunctionNodeCommand(
    const std::string& id,
    Node fun,
    const std::vector<Node>& formals,
    Node formula)
    : d_id(id), d_fun(fun), d_formals(formals), d_formula(formula)
{
}

void DefineFunctionNodeCommand::toStream(std::ostream& out,
                                         int toDepth,
                                         bool types,
                                         size_t dag,
                                         OutputLanguage language) const
{
  TypeNode tn = d_fun.getType();
  bool hasRange =
      (tn.isFunction() || tn.isConstructor() || tn.isSelector());
  Printer::getPrinter(language)->toStreamCmdDefineFunction(
      out,
      d_fun.toString(),
      d_formals,
      (hasRange ? d_fun.getType().getRangeType() : tn),
      d_formula);
}

NodeCommand* DefineFunctionNodeCommand::clone() const
{
  return new DefineFunctionNodeCommand(d_id, d_fun, d_formals, d_formula);
}

}  // namespace CVC4
