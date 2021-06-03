/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the AST output language.
 */
#include "printer/ast/ast_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/node_manager_attributes.h"  // for VarNameAttr
#include "expr/node_visitor.h"
#include "options/language.h"  // for LANG_AST
#include "printer/let_binding.h"
#include "smt/command.h"
#include "smt/node_command.h"

using namespace std;

namespace cvc5 {
namespace printer {
namespace ast {

void AstPrinter::toStream(std::ostream& out,
                          TNode n,
                          int toDepth,
                          size_t dag) const
{
  if(dag != 0) {
    LetBinding lbind(dag + 1);
    toStreamWithLetify(out, n, toDepth, &lbind);
  } else {
    toStream(out, n, toDepth);
  }
}

void AstPrinter::toStream(std::ostream& out,
                          TNode n,
                          int toDepth,
                          LetBinding* lbind) const
{
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  // variable
  if(n.getMetaKind() == kind::metakind::VARIABLE) {
    string s;
    if(n.getAttribute(expr::VarNameAttr(), s)) {
      out << s;
    } else {
      out << "var_" << n.getId();
    }
    return;
  }

  out << '(' << n.getKind();
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    // constant
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, n);
  }
  else if (n.isClosure())
  {
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      // body is re-letified
      if (i == 1)
      {
        toStreamWithLetify(out, n[i], toDepth, lbind);
        continue;
      }
      toStream(out, n[i], toDepth < 0 ? toDepth : toDepth - 1, lbind);
    }
  }
  else
  {
    // operator
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      out << ' ';
      if(toDepth != 0) {
        toStream(
            out, n.getOperator(), toDepth < 0 ? toDepth : toDepth - 1, lbind);
      } else {
        out << "(...)";
      }
    }
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      if(i != iend) {
        out << ' ';
      }
      if(toDepth != 0) {
        toStream(out, *i, toDepth < 0 ? toDepth : toDepth - 1, lbind);
      } else {
        out << "(...)";
      }
    }
  }
  out << ')';
}/* AstPrinter::toStream(TNode) */

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s);

void AstPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  if(tryToStream<CommandSuccess>(out, s) ||
     tryToStream<CommandFailure>(out, s) ||
     tryToStream<CommandUnsupported>(out, s) ||
     tryToStream<CommandInterrupted>(out, s)) {
    return;
  }

  out << "ERROR: don't know how to print a CommandStatus of class: "
      << typeid(*s).name() << endl;

}/* AstPrinter::toStream(CommandStatus*) */

void AstPrinter::toStream(std::ostream& out, const smt::Model& m) const
{
  out << "Model()";
}

void AstPrinter::toStreamModelSort(std::ostream& out,
                                   const smt::Model& m,
                                   TypeNode tn) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void AstPrinter::toStreamModelTerm(std::ostream& out,
                                   const smt::Model& m,
                                   Node n) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void AstPrinter::toStreamCmdEmpty(std::ostream& out,
                                  const std::string& name) const
{
  out << "EmptyCommand(" << name << ')' << std::endl;
}

void AstPrinter::toStreamCmdEcho(std::ostream& out,
                                 const std::string& output) const
{
  out << "EchoCommand(" << output << ')' << std::endl;
}

void AstPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "Assert(" << n << ')' << std::endl;
}

void AstPrinter::toStreamCmdPush(std::ostream& out) const
{
  out << "Push()" << std::endl;
}

void AstPrinter::toStreamCmdPop(std::ostream& out) const {
  out << "Pop()" << std::endl;
}

void AstPrinter::toStreamCmdCheckSat(std::ostream& out, Node n) const
{
  if (n.isNull())
  {
    out << "CheckSat()";
  }
  else
  {
    out << "CheckSat(" << n << ')';
  }
  out << std::endl;
}

void AstPrinter::toStreamCmdCheckSatAssuming(
    std::ostream& out, const std::vector<Node>& nodes) const
{
  out << "CheckSatAssuming( << ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, ", "));
  out << ">> )" << std::endl;
}

void AstPrinter::toStreamCmdQuery(std::ostream& out, Node n) const
{
  out << "Query(" << n << ')' << std::endl;
}

void AstPrinter::toStreamCmdReset(std::ostream& out) const
{
  out << "Reset()" << std::endl;
}

void AstPrinter::toStreamCmdResetAssertions(std::ostream& out) const
{
  out << "ResetAssertions()" << std::endl;
}

void AstPrinter::toStreamCmdQuit(std::ostream& out) const
{
  out << "Quit()" << std::endl;
}

void AstPrinter::toStreamCmdDeclarationSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  out << "DeclarationSequence[" << endl;
  for (CommandSequence::const_iterator i = sequence.cbegin();
       i != sequence.cend();
       ++i)
  {
    out << *i << endl;
  }
  out << "]" << std::endl;
}

void AstPrinter::toStreamCmdCommandSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  out << "CommandSequence[" << endl;
  for (CommandSequence::const_iterator i = sequence.cbegin();
       i != sequence.cend();
       ++i)
  {
    out << *i << endl;
  }
  out << "]" << std::endl;
}

void AstPrinter::toStreamCmdDeclareFunction(std::ostream& out,
                                            const std::string& id,
                                            TypeNode type) const
{
  out << "Declare(" << id << "," << type << ')' << std::endl;
}

void AstPrinter::toStreamCmdDefineFunction(std::ostream& out,
                                           const std::string& id,
                                           const std::vector<Node>& formals,
                                           TypeNode range,
                                           Node formula) const
{
  out << "DefineFunction( \"" << id << "\", [";
  if (formals.size() > 0)
  {
    copy(formals.begin(), formals.end() - 1, ostream_iterator<Node>(out, ", "));
    out << formals.back();
  }
  out << "], << " << formula << " >> )" << std::endl;
}

void AstPrinter::toStreamCmdDeclareType(std::ostream& out,
                                        TypeNode type) const
{
  out << "DeclareType(" << type << ')' << std::endl;
}

void AstPrinter::toStreamCmdDefineType(std::ostream& out,
                                       const std::string& id,
                                       const std::vector<TypeNode>& params,
                                       TypeNode t) const
{
  out << "DefineType(" << id << ",[";
  if (params.size() > 0)
  {
    copy(params.begin(),
         params.end() - 1,
         ostream_iterator<TypeNode>(out, ", "));
    out << params.back();
  }
  out << "]," << t << ')' << std::endl;
}

void AstPrinter::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  out << "Simplify( << " << n << " >> )" << std::endl;
}

void AstPrinter::toStreamCmdGetValue(std::ostream& out,
                                     const std::vector<Node>& nodes) const
{
  out << "GetValue( << ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, ", "));
  out << ">> )" << std::endl;
}

void AstPrinter::toStreamCmdGetModel(std::ostream& out) const
{
  out << "GetModel()" << std::endl;
}

void AstPrinter::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "GetAssignment()" << std::endl;
}

void AstPrinter::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "GetAssertions()" << std::endl;
}

void AstPrinter::toStreamCmdGetProof(std::ostream& out) const
{
  out << "GetProof()" << std::endl;
}

void AstPrinter::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "GetUnsatCore()" << std::endl;
}

void AstPrinter::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                               Result::Sat status) const
{
  out << "SetBenchmarkStatus(" << status << ')' << std::endl;
}

void AstPrinter::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                              const std::string& logic) const
{
  out << "SetBenchmarkLogic(" << logic << ')' << std::endl;
}

void AstPrinter::toStreamCmdSetInfo(std::ostream& out,
                                    const std::string& flag,
                                    const std::string& value) const
{
  out << "SetInfo(" << flag << ", " << value << ')' << std::endl;
}

void AstPrinter::toStreamCmdGetInfo(std::ostream& out,
                                    const std::string& flag) const
{
  out << "GetInfo(" << flag << ')' << std::endl;
}

void AstPrinter::toStreamCmdSetOption(std::ostream& out,
                                      const std::string& flag,
                                      const std::string& value) const
{
  out << "SetOption(" << flag << ", " << value << ')' << std::endl;
}

void AstPrinter::toStreamCmdGetOption(std::ostream& out,
                                      const std::string& flag) const
{
  out << "GetOption(" << flag << ')' << std::endl;
}

void AstPrinter::toStreamCmdDatatypeDeclaration(
    std::ostream& out, const std::vector<TypeNode>& datatypes) const
{
  out << "DatatypeDeclarationCommand([";
  for (const TypeNode& t : datatypes)
  {
    out << t << ";" << endl;
  }
  out << "])" << std::endl;
}

void AstPrinter::toStreamCmdComment(std::ostream& out,
                                    const std::string& comment) const
{
  out << "CommentCommand([" << comment << "])" << std::endl;
}

void AstPrinter::toStreamWithLetify(std::ostream& out,
                                    Node n,
                                    int toDepth,
                                    LetBinding* lbind) const
{
  if (lbind == nullptr)
  {
    toStream(out, n, toDepth);
    return;
  }
  std::stringstream cparen;
  std::vector<Node> letList;
  lbind->letify(n, letList);
  if (!letList.empty())
  {
    std::map<Node, uint32_t>::const_iterator it;
    out << "(LET ";
    cparen << ")";
    bool first = true;
    for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
    {
      if (!first)
      {
        out << ", ";
      }
      else
      {
        first = false;
      }
      Node nl = letList[i];
      uint32_t id = lbind->getId(nl);
      out << "_let_" << id << " := ";
      Node nlc = lbind->convert(nl, "_let_", false);
      toStream(out, nlc, toDepth, lbind);
    }
    out << " IN ";
  }
  Node nc = lbind->convert(n, "_let_");
  // print the body, passing the lbind object
  toStream(out, nc, toDepth, lbind);
  out << cparen.str();
  lbind->popScope();
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c)
{
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

static void toStream(std::ostream& out, const CommandSuccess* s)
{
  if(Command::printsuccess::getPrintSuccess(out)) {
    out << "OK" << endl;
  }
}

static void toStream(std::ostream& out, const CommandInterrupted* s)
{
  out << "INTERRUPTED" << endl;
}

static void toStream(std::ostream& out, const CommandUnsupported* s)
{
  out << "UNSUPPORTED" << endl;
}

static void toStream(std::ostream& out, const CommandFailure* s)
{
  out << s->getMessage() << endl;
}

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s)
{
  if(typeid(*s) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(s));
    return true;
  }
  return false;
}

}  // namespace ast
}  // namespace printer
}  // namespace cvc5
