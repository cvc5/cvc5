/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the AST output language.
 */
#include "printer/ast/ast_printer.h"

#include <iostream>
#include <sstream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/node_visitor.h"
#include "options/io_utils.h"
#include "options/language.h"  // for LANG_AST
#include "printer/let_binding.h"

using namespace std;

namespace cvc5::internal {
namespace printer {
namespace ast {

void AstPrinter::toStream(std::ostream& out, TNode n) const
{
  size_t dag = options::ioutils::getDagThresh(out);
  int toDepth = options::ioutils::getNodeDepth(out);
  if(dag != 0) {
    LetBinding lbind(dag + 1);
    toStreamWithLetify(out, n, toDepth, &lbind);
  } else {
    toStream(out, n, toDepth);
  }
}

void AstPrinter::toStream(std::ostream& out, Kind k) const
{
  out << kind::kindToString(k);
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
    if (n.hasName())
    {
      out << n.getName();
    }
    else
    {
      out << "var_" << n.getId();
    }
    return;
  }

  out << '(' << n.getKind();
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    // constant
    out << ' ';
    n.constToStream(out);
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

void AstPrinter::toStream(std::ostream& out, const smt::Model& m) const
{
  out << "Model(" << std::endl;
  this->Printer::toStream(out, m);
  out << ")" << std::endl;
}

void AstPrinter::toStreamModelSort(std::ostream& out,
                                   TypeNode tn,
                                   const std::vector<Node>& elements) const
{
  out << "(" << tn << "(";
  bool firstTime = true;
  for (const Node& elem : elements)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << " ";
    }
    out << elem;
  }
  out << "))" << std::endl;
}

void AstPrinter::toStreamModelTerm(std::ostream& out,
                                   const Node& n,
                                   const Node& value) const
{
  out << "(" << n << " " << value << ")" << std::endl;
}

void AstPrinter::toStreamCmdSuccess(std::ostream& out) const
{
  out << "OK" << endl;
}

void AstPrinter::toStreamCmdInterrupted(std::ostream& out) const
{
  out << "INTERRUPTED" << endl;
}

void AstPrinter::toStreamCmdUnsupported(std::ostream& out) const
{
  out << "UNSUPPORTED" << endl;
}

void AstPrinter::toStreamCmdFailure(std::ostream& out,
                                    const std::string& message) const
{
  out << message << endl;
}

void AstPrinter::toStreamCmdRecoverableFailure(std::ostream& out,
                                               const std::string& message) const
{
  out << message << endl;
}

void AstPrinter::toStreamCmdEmpty(std::ostream& out,
                                  const std::string& name) const
{
  out << "Emptycvc5::Command(" << name << ')' << std::endl;
}

void AstPrinter::toStreamCmdEcho(std::ostream& out,
                                 const std::string& output) const
{
  out << "Echocvc5::Command(" << output << ')' << std::endl;
}

void AstPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "Assert(" << n << ')' << std::endl;
}

void AstPrinter::toStreamCmdPush(std::ostream& out, uint32_t nscopes) const
{
  out << "Push(" << nscopes << ")" << std::endl;
}

void AstPrinter::toStreamCmdPop(std::ostream& out, uint32_t nscopes) const
{
  out << "Pop(" << nscopes << ")" << std::endl;
}

void AstPrinter::toStreamCmdCheckSat(std::ostream& out) const
{
  out << "CheckSat()" << std::endl;
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

void AstPrinter::toStreamCmdGetProof(std::ostream& out,
                                     modes::ProofComponent c) const
{
  out << "GetProof(" << c << ")" << std::endl;
}

void AstPrinter::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "GetUnsatCore()" << std::endl;
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
  out << "DatatypeDeclarationcvc5::Command([";
  for (const TypeNode& t : datatypes)
  {
    out << t << ";" << endl;
  }
  out << "])" << std::endl;
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

}  // namespace ast
}  // namespace printer
}  // namespace cvc5::internal
