/*********************                                                        */
/*! \file ast_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the AST output language
 **
 ** The pretty-printer interface for the AST output language.
 **/
#include "printer/ast/ast_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/expr.h"                     // for ExprSetDepth etc..
#include "expr/node_manager_attributes.h"  // for VarNameAttr
#include "expr/node_visitor.h"
#include "options/language.h"  // for LANG_AST
#include "printer/dagification_visitor.h"
#include "smt/command.h"
#include "smt/node_command.h"
#include "theory/substitutions.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace ast {

void AstPrinter::toStream(
    std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const
{
  if(dag != 0) {
    DagificationVisitor dv(dag);
    NodeVisitor<DagificationVisitor> visitor;
    visitor.run(dv, n);
    const theory::SubstitutionMap& lets = dv.getLets();
    if(!lets.empty()) {
      out << "(LET ";
      bool first = true;
      for(theory::SubstitutionMap::const_iterator i = lets.begin();
          i != lets.end();
          ++i) {
        if(! first) {
          out << ", ";
        } else {
          first = false;
        }
        toStream(out, (*i).second, toDepth, types, false);
        out << " := ";
        toStream(out, (*i).first, toDepth, types, false);
      }
      out << " IN ";
    }
    Node body = dv.getDagifiedBody();
    toStream(out, body, toDepth, types);
    if(!lets.empty()) {
      out << ')';
    }
  } else {
    toStream(out, n, toDepth, types);
  }
}

void AstPrinter::toStream(std::ostream& out,
                          TNode n,
                          int toDepth,
                          bool types) const
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
    if(types) {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, language::output::LANG_AST);
    }

    return;
  }

  out << '(' << n.getKind();
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    // constant
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, n);
  } else {
    // operator
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      out << ' ';
      if(toDepth != 0) {
        toStream(out, n.getOperator(), toDepth < 0 ? toDepth : toDepth - 1, types);
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
        toStream(out, *i, toDepth < 0 ? toDepth : toDepth - 1, types);
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

void AstPrinter::toStream(std::ostream& out, const Model& m) const
{
  out << "Model()";
}

void AstPrinter::toStream(std::ostream& out,
                          const Model& m,
                          const NodeCommand* c) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void AstPrinter::toStreamCmdEmpty(std::ostream& out,
                                  const std::string& name) const
{
  out << "EmptyCommand(" << name << ')';
}

void AstPrinter::toStreamCmdEcho(std::ostream& out,
                                 const std::string& output) const
{
  out << "EchoCommand(" << output << ')';
}

void AstPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "Assert(" << n << ')';
}

void AstPrinter::toStreamCmdPush(std::ostream& out) const { out << "Push()"; }

void AstPrinter::toStreamCmdPop(std::ostream& out) const { out << "Pop()"; }

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
}

void AstPrinter::toStreamCmdCheckSatAssuming(
    std::ostream& out, const std::vector<Node>& nodes) const
{
  out << "CheckSatAssuming( << ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, ", "));
  out << ">> )";
}

void AstPrinter::toStreamCmdQuery(std::ostream& out, Node n) const
{
  out << "Query(" << n << ')';
}

void AstPrinter::toStreamCmdReset(std::ostream& out) const { out << "Reset()"; }

void AstPrinter::toStreamCmdResetAssertions(std::ostream& out) const
{
  out << "ResetAssertions()";
}

void AstPrinter::toStreamCmdQuit(std::ostream& out) const { out << "Quit()"; }

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
  out << "]";
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
  out << "]";
}

void AstPrinter::toStreamCmdDeclareFunction(std::ostream& out,
                                            const std::string& id,
                                            TypeNode type) const
{
  out << "Declare(" << id << "," << type << ')';
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
  out << "], << " << formula << " >> )";
}

void AstPrinter::toStreamCmdDeclareType(std::ostream& out,
                                        const std::string& id,
                                        size_t arity,
                                        TypeNode type) const
{
  out << "DeclareType(" << id << "," << arity << "," << type << ')';
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
  out << "]," << t << ')';
}

void AstPrinter::toStreamCmdDefineNamedFunction(
    std::ostream& out,
    const std::string& id,
    const std::vector<Node>& formals,
    TypeNode range,
    Node formula) const
{
  out << "DefineNamedFunction( ";
  toStreamCmdDefineFunction(out, id, formals, range, formula);
  out << " )" << std::endl;
}

void AstPrinter::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  out << "Simplify( << " << n << " >> )";
}

void AstPrinter::toStreamCmdGetValue(std::ostream& out,
                                     const std::vector<Node>& nodes) const
{
  out << "GetValue( << ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, ", "));
  out << ">> )";
}

void AstPrinter::toStreamCmdGetModel(std::ostream& out) const
{
  out << "GetModel()";
}

void AstPrinter::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "GetAssignment()";
}

void AstPrinter::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "GetAssertions()";
}

void AstPrinter::toStreamCmdGetProof(std::ostream& out) const
{
  out << "GetProof()";
}

void AstPrinter::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "GetUnsatCore()";
}

void AstPrinter::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                               Result::Sat status) const
{
  out << "SetBenchmarkStatus(" << status << ')';
}

void AstPrinter::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                              const std::string& logic) const
{
  out << "SetBenchmarkLogic(" << logic << ')';
}

void AstPrinter::toStreamCmdSetInfo(std::ostream& out,
                                    const std::string& flag,
                                    SExpr sexpr) const
{
  out << "SetInfo(" << flag << ", " << sexpr << ')';
}

void AstPrinter::toStreamCmdGetInfo(std::ostream& out,
                                    const std::string& flag) const
{
  out << "GetInfo(" << flag << ')';
}

void AstPrinter::toStreamCmdSetOption(std::ostream& out,
                                      const std::string& flag,
                                      SExpr sexpr) const
{
  out << "SetOption(" << flag << ", " << sexpr << ')';
}

void AstPrinter::toStreamCmdGetOption(std::ostream& out,
                                      const std::string& flag) const
{
  out << "GetOption(" << flag << ')';
}

void AstPrinter::toStreamCmdDatatypeDeclaration(
    std::ostream& out, const std::vector<TypeNode>& datatypes) const
{
  out << "DatatypeDeclarationCommand([";
  for (const TypeNode& t : datatypes)
  {
    out << t << ";" << endl;
  }
  out << "])";
}

void AstPrinter::toStreamCmdComment(std::ostream& out,
                                    const std::string& comment) const
{
  out << "CommentCommand([" << comment << "])";
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

}/* CVC4::printer::ast namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
