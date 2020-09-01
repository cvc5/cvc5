/*********************                                                        */
/*! \file printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/
#include "printer/printer.h"

#include <string>

#include "options/base_options.h"
#include "options/language.h"
#include "printer/ast/ast_printer.h"
#include "printer/cvc/cvc_printer.h"
#include "printer/smt2/smt2_printer.h"
#include "printer/tptp/tptp_printer.h"
#include "smt/node_command.h"

using namespace std;

namespace CVC4 {

unique_ptr<Printer> Printer::d_printers[language::output::LANG_MAX];

unique_ptr<Printer> Printer::makePrinter(OutputLanguage lang)
{
  using namespace CVC4::language::output;

  switch(lang) {
  case LANG_SMTLIB_V2_0:
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::smt2_0_variant));

  case LANG_SMTLIB_V2_5:
    return unique_ptr<Printer>(new printer::smt2::Smt2Printer());

  case LANG_SMTLIB_V2_6:
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant));

  case LANG_TPTP:
    return unique_ptr<Printer>(new printer::tptp::TptpPrinter());

  case LANG_CVC4:
    return unique_ptr<Printer>(new printer::cvc::CvcPrinter());

  case LANG_SYGUS_V2:
    // sygus version 2.0 does not have discrepancies with smt2, hence we use
    // a normal smt2 variant here.
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant));

  case LANG_AST:
    return unique_ptr<Printer>(new printer::ast::AstPrinter());

  case LANG_CVC3:
    return unique_ptr<Printer>(
        new printer::cvc::CvcPrinter(/* cvc3-mode = */ true));

  default: Unhandled() << lang;
  }
}

void Printer::toStream(std::ostream& out, const Model& m) const
{
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    const NodeCommand* cmd = m.getCommand(i);
    const DeclareFunctionNodeCommand* dfc =
        dynamic_cast<const DeclareFunctionNodeCommand*>(cmd);
    if (dfc != NULL && !m.isModelCoreSymbol(dfc->getFunction().toExpr()))
    {
      continue;
    }
    toStream(out, m, cmd);
  }
}/* Printer::toStream(Model) */

void Printer::toStream(std::ostream& out, const UnsatCore& core) const
{
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    toStreamCmdAssert(out, Node::fromExpr(*i));
    out << std::endl;
  }
}/* Printer::toStream(UnsatCore) */

Printer* Printer::getPrinter(OutputLanguage lang)
{
  if(lang == language::output::LANG_AUTO) {
  // Infer the language to use for output.
  //
  // Options can be null in certain circumstances (e.g., when printing
  // the singleton "null" expr.  So we guard against segfault
  if(not Options::isCurrentNull()) {
    if(options::outputLanguage.wasSetByUser()) {
      lang = options::outputLanguage();
    }
    if(lang == language::output::LANG_AUTO && options::inputLanguage.wasSetByUser()) {
      lang = language::toOutputLanguage(options::inputLanguage());
     }
   }
   if (lang == language::output::LANG_AUTO)
   {
     lang = language::output::LANG_SMTLIB_V2_6;  // default
   }
  }
  if(d_printers[lang] == NULL) {
    d_printers[lang] = makePrinter(lang);
  }
  return d_printers[lang].get();
}

void Printer::printUnknownCommand(std::ostream& out,
                                  const std::string& name) const
{
  out << "ERROR: don't know how to print " << name << " command" << std::endl;
}

void Printer::toStreamCmdEmpty(std::ostream& out, const std::string& name) const
{
  printUnknownCommand(out, "empty");
}

void Printer::toStreamCmdEcho(std::ostream& out,
                              const std::string& output) const
{
  printUnknownCommand(out, "echo");
}

void Printer::toStreamCmdAssert(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "assert");
}

void Printer::toStreamCmdPush(std::ostream& out) const
{
  printUnknownCommand(out, "push");
}

void Printer::toStreamCmdPop(std::ostream& out) const
{
  printUnknownCommand(out, "pop");
}

void Printer::toStreamCmdDeclareFunction(std::ostream& out,
                                         const std::string& id,
                                         TypeNode type) const
{
  printUnknownCommand(out, "declare-fun");
}

void Printer::toStreamCmdDeclareType(std::ostream& out,
                                     const std::string& id,
                                     size_t arity,
                                     TypeNode type) const
{
  printUnknownCommand(out, "declare-sort");
}

void Printer::toStreamCmdDefineType(std::ostream& out,
                                    const std::string& id,
                                    const std::vector<TypeNode>& params,
                                    TypeNode t) const
{
  printUnknownCommand(out, "define-sort");
}

void Printer::toStreamCmdDefineFunction(std::ostream& out,
                                        const std::string& id,
                                        const std::vector<Node>& formals,
                                        TypeNode range,
                                        Node formula) const
{
  printUnknownCommand(out, "define-fun");
}

void Printer::toStreamCmdDefineNamedFunction(std::ostream& out,
                                             const std::string& id,
                                             const std::vector<Node>& formals,
                                             TypeNode range,
                                             Node formula) const
{
  printUnknownCommand(out, "define-named-function");
}

void Printer::toStreamCmdDefineFunctionRec(
    std::ostream& out,
    const std::vector<Node>& funcs,
    const std::vector<std::vector<Node>>& formals,
    const std::vector<Node>& formulas) const
{
  printUnknownCommand(out, "define-fun-rec");
}

void Printer::toStreamCmdSetUserAttribute(std::ostream& out,
                                          const std::string& attr,
                                          Node n) const
{
  printUnknownCommand(out, "set-user-attribute");
}

void Printer::toStreamCmdCheckSat(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "check-sat");
}

void Printer::toStreamCmdCheckSatAssuming(std::ostream& out,
                                          const std::vector<Node>& nodes) const
{
  printUnknownCommand(out, "check-sat-assuming");
}

void Printer::toStreamCmdQuery(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "query");
}

void Printer::toStreamCmdDeclareVar(std::ostream& out,
                                    Node var,
                                    TypeNode type) const
{
  printUnknownCommand(out, "declare-var");
}

void Printer::toStreamCmdSynthFun(std::ostream& out,
                                  const std::string& sym,
                                  const std::vector<Node>& vars,
                                  TypeNode range,
                                  bool isInv,
                                  TypeNode sygusType) const
{
  printUnknownCommand(out, isInv ? "synth-inv" : "synth-fun");
}

void Printer::toStreamCmdConstraint(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "constraint");
}

void Printer::toStreamCmdInvConstraint(
    std::ostream& out, Node inv, Node pre, Node trans, Node post) const
{
  printUnknownCommand(out, "inv-constraint");
}

void Printer::toStreamCmdCheckSynth(std::ostream& out) const
{
  printUnknownCommand(out, "check-synth");
}

void Printer::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "simplify");
}

void Printer::toStreamCmdExpandDefinitions(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "expand-definitions");
}

void Printer::toStreamCmdGetValue(std::ostream& out,
                                  const std::vector<Node>& nodes) const
{
  printUnknownCommand(out, "get-value");
}

void Printer::toStreamCmdGetAssignment(std::ostream& out) const
{
  printUnknownCommand(out, "get-assignment");
}

void Printer::toStreamCmdGetModel(std::ostream& out) const
{
  printUnknownCommand(out, "ge-model");
}

void Printer::toStreamCmdBlockModel(std::ostream& out) const
{
  printUnknownCommand(out, "block-model");
}

void Printer::toStreamCmdBlockModelValues(std::ostream& out,
                                          const std::vector<Node>& nodes) const
{
  printUnknownCommand(out, "block-model-values");
}

void Printer::toStreamCmdGetProof(std::ostream& out) const
{
  printUnknownCommand(out, "get-proof");
}

void Printer::toStreamCmdGetInstantiations(std::ostream& out) const
{
  printUnknownCommand(out, "get-instantiations");
}

void Printer::toStreamCmdGetSynthSolution(std::ostream& out) const
{
  printUnknownCommand(out, "get-synth-solution");
}

void Printer::toStreamCmdGetInterpol(std::ostream& out,
                                     const std::string& name,
                                     Node conj,
                                     TypeNode sygusType) const
{
  printUnknownCommand(out, "get-interpol");
}

void Printer::toStreamCmdGetAbduct(std::ostream& out,
                                   const std::string& name,
                                   Node conj,
                                   TypeNode sygusType) const
{
  printUnknownCommand(out, "get-abduct");
}

void Printer::toStreamCmdGetQuantifierElimination(std::ostream& out,
                                                  Node n) const
{
  printUnknownCommand(out, "get-quantifier-elimination");
}

void Printer::toStreamCmdGetUnsatAssumptions(std::ostream& out) const
{
  printUnknownCommand(out, "get-unsat-assumption");
}

void Printer::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  printUnknownCommand(out, "get-unsat-core");
}

void Printer::toStreamCmdGetAssertions(std::ostream& out) const
{
  printUnknownCommand(out, "get-assertions");
}

void Printer::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                            BenchmarkStatus status) const
{
  printUnknownCommand(out, "set-info");
}

void Printer::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                           const std::string& logic) const
{
  printUnknownCommand(out, "set-logic");
}

void Printer::toStreamCmdSetInfo(std::ostream& out,
                                 const std::string& flag,
                                 SExpr sexpr) const
{
  printUnknownCommand(out, "set-info");
}

void Printer::toStreamCmdGetInfo(std::ostream& out,
                                 const std::string& flag) const
{
  printUnknownCommand(out, "get-info");
}

void Printer::toStreamCmdSetOption(std::ostream& out,
                                   const std::string& flag,
                                   SExpr sexpr) const
{
  printUnknownCommand(out, "set-option");
}

void Printer::toStreamCmdGetOption(std::ostream& out,
                                   const std::string& flag) const
{
  printUnknownCommand(out, "get-option");
}

void Printer::toStreamCmdSetExpressionName(std::ostream& out,
                                           Node n,
                                           const std::string& name) const
{
  printUnknownCommand(out, "set-expression-name");
}

void Printer::toStreamCmdDatatypeDeclaration(
    std::ostream& out, const std::vector<TypeNode>& datatypes) const
{
  printUnknownCommand(
      out, datatypes.size() == 1 ? "declare-datatype" : "declare-datatypes");
}

void Printer::toStreamCmdReset(std::ostream& out) const
{
  printUnknownCommand(out, "reset");
}

void Printer::toStreamCmdResetAssertions(std::ostream& out) const
{
  printUnknownCommand(out, "reset-assertions");
}

void Printer::toStreamCmdQuit(std::ostream& out) const
{
  printUnknownCommand(out, "quit");
}

void Printer::toStreamCmdComment(std::ostream& out,
                                 const std::string& comment) const
{
  printUnknownCommand(out, "comment");
}

void Printer::toStreamCmdCommandSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  printUnknownCommand(out, "sequence");
}

void Printer::toStreamCmdDeclarationSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  printUnknownCommand(out, "sequence");
}

}/* CVC4 namespace */
