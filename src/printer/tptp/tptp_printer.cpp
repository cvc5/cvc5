/*********************                                                        */
/*! \file tptp_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the TPTP output language
 **
 ** The pretty-printer interface for the TPTP output language.
 **/
#include "printer/tptp/tptp_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/expr.h" // for ExprSetDepth etc..
#include "expr/node_manager.h" // for VarNameAttr
#include "options/language.h" // for LANG_AST
#include "options/smt_options.h" // for unsat cores
#include "smt/smt_engine.h"
#include "smt/command.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace tptp {

void TptpPrinter::toStream(
    std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const
{
  n.toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  s->toStream(out, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const Model& m) const
{
  std::string statusName(m.isKnownSat() ? "FiniteModel"
                                        : "CandidateFiniteModel");
  out << "% SZS output start " << statusName << " for " << m.getInputName()
      << endl;
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    this->Printer::toStreamUsing(language::output::LANG_SMTLIB_V2_5, out, m, m.getCommand(i));
  }
  out << "% SZS output end " << statusName << " for " << m.getInputName()
      << endl;
}

void TptpPrinter::toStream(std::ostream& out,
                           const Model& m,
                           const Command* c) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}
void TptpPrinter::toStream(std::ostream& out, const UnsatCore& core) const
{
  out << "% SZS output start UnsatCore " << std::endl;
  SmtEngine * smt = core.getSmtEngine();
  Assert(smt != NULL);
  for(UnsatCore::const_iterator i = core.begin(); i != core.end(); ++i) {
    std::string name;
    if (smt->getExpressionName(*i, name)) {
      // Named assertions always get printed
      out << name << endl;
    } else if (options::dumpUnsatCoresFull()) {
      // Unnamed assertions only get printed if the option is set
      out << *i << endl;
    }
  }
  out << "% SZS output end UnsatCore " << std::endl;
}

void TptpPrinter::toStreamCmdEmpty(std::ostream& out,
                                   const std::string& name) const
{
  printUnknownCommand(out, "empty");
}

void TptpPrinter::toStreamCmdEcho(std::ostream& out,
                                  const std::string& output) const
{
  printUnknownCommand(out, "echo");
}

void TptpPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "assert");
}

void TptpPrinter::toStreamCmdPush(std::ostream& out) const
{
  printUnknownCommand(out, "push");
}

void TptpPrinter::toStreamCmdPop(std::ostream& out) const
{
  printUnknownCommand(out, "pop");
}

void TptpPrinter::toStreamCmdDeclareFunction(std::ostream& out,
                                             const std::string& id,
                                             TypeNode type) const
{
  printUnknownCommand(out, "declare-fun");
}

void TptpPrinter::toStreamCmdDeclareType(std::ostream& out,
                                         const std::string& id,
                                         size_t arity,
                                         TypeNode type) const
{
  printUnknownCommand(out, "declare-sort");
}

void TptpPrinter::toStreamCmdDefineType(std::ostream& out,
                                        const std::string& id,
                                        const std::vector<TypeNode>& params,
                                        TypeNode t) const
{
  printUnknownCommand(out, "define-sort");
}

void TptpPrinter::toStreamCmdDefineFunction(std::ostream& out,
                                            const std::string& id,
                                            const std::vector<Node>& formals,
                                            TypeNode range,
                                            Node formula) const
{
  printUnknownCommand(out, "define-fun");
}

void TptpPrinter::toStreamCmdDefineNamedFunction(
    std::ostream& out,
    const std::string& id,
    const std::vector<Node>& formals,
    TypeNode range,
    Node formula) const
{
  printUnknownCommand(out, "define-named-function");
}

void TptpPrinter::toStreamCmdCheckSat(std::ostream& out) const
{
  printUnknownCommand(out, "check-sat");
}

void TptpPrinter::toStreamCmdCheckSat(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "check-sat");
}

void TptpPrinter::toStreamCmdCheckSatAssuming(std::ostream& out,
                                              std::vector<Node> nodes) const
{
  printUnknownCommand(out, "check-sat-assuming");
}

void TptpPrinter::toStreamCmdQuery(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "query");
}

void TptpPrinter::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "simplify");
}

void TptpPrinter::toStreamCmdGetValue(std::ostream& out,
                                      const std::vector<Node>& nodes) const
{
  printUnknownCommand(out, "get-value");
}

void TptpPrinter::toStreamCmdGetAssignment(std::ostream& out) const
{
  printUnknownCommand(out, "get-assignment");
}

void TptpPrinter::toStreamCmdGetModel(std::ostream& out) const
{
  printUnknownCommand(out, "ge-model");
}

void TptpPrinter::toStreamCmdGetProof(std::ostream& out) const
{
  printUnknownCommand(out, "get-proof");
}

void TptpPrinter::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  printUnknownCommand(out, "get-unsat-core");
}

void TptpPrinter::toStreamCmdGetAssertions(std::ostream& out) const
{
  printUnknownCommand(out, "get-assertions");
}

void TptpPrinter::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                                BenchmarkStatus status) const
{
  printUnknownCommand(out, "set-info");
}

void TptpPrinter::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                               const std::string& logic) const
{
  printUnknownCommand(out, "set-logic");
}

void TptpPrinter::toStreamCmdSetInfo(std::ostream& out,
                                     const std::string& flag,
                                     SExpr sexpr) const
{
  printUnknownCommand(out, "set-info");
}

void TptpPrinter::toStreamCmdGetInfo(std::ostream& out,
                                     const std::string& flag) const
{
  printUnknownCommand(out, "get-info");
}

void TptpPrinter::toStreamCmdSetOption(std::ostream& out,
                                       const std::string& flag,
                                       SExpr sexpr) const
{
  printUnknownCommand(out, "set-option");
}

void TptpPrinter::toStreamCmdGetOption(std::ostream& out,
                                       const std::string& flag) const
{
  printUnknownCommand(out, "get-option");
}

void TptpPrinter::toStreamCmdDatatypeDeclaration(
    std::ostream& out, const std::vector<TypeNode>& datatypes) const
{
  printUnknownCommand(
      out, datatypes.size() == 1 ? "declare-datatype" : "declare-datatypes");
}

void TptpPrinter::toStreamCmdReset(std::ostream& out) const
{
  printUnknownCommand(out, "reset");
}

void TptpPrinter::toStreamCmdResetAssertions(std::ostream& out) const
{
  printUnknownCommand(out, "reset-assertions");
}

void TptpPrinter::toStreamCmdQuit(std::ostream& out) const
{
  printUnknownCommand(out, "quit");
}

void TptpPrinter::toStreamCmdComment(std::ostream& out,
                                     const std::string& comment) const
{
  printUnknownCommand(out, "comment");
}

void TptpPrinter::toStreamCmdCommandSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  printUnknownCommand(out, "sequence");
}

void TptpPrinter::toStreamCmdDeclarationSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  printUnknownCommand(out, "sequence");
}

}/* CVC4::printer::tptp namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
