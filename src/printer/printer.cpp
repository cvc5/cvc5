/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base of the pretty-printer interface.
 */
#include "printer/printer.h"

#include <sstream>
#include <string>

#include "expr/node.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/printer_options.h"
#include "printer/ast/ast_printer.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/unsat_core.h"
#include "smt/model.h"
#include "theory/quantifiers/instantiation_list.h"

using namespace std;

namespace cvc5::internal {

unique_ptr<Printer>
    Printer::d_printers[static_cast<size_t>(Language::LANG_MAX)];

unique_ptr<Printer> Printer::makePrinter(Language lang)
{
  switch(lang) {
    case Language::LANG_SMTLIB_V2_6:
      return unique_ptr<Printer>(
          new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant));

    case Language::LANG_SYGUS_V2:
      // sygus version 2.0 does not have discrepancies with smt2, hence we use
      // a normal smt2 variant here.
      return unique_ptr<Printer>(
          new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant));

    case Language::LANG_AST:
      return unique_ptr<Printer>(new printer::ast::AstPrinter());

    default: Unhandled() << lang;
  }
}

void Printer::toStream(std::ostream& out, const smt::Model& m) const
{
  // print the declared sorts
  const std::vector<TypeNode>& dsorts = m.getDeclaredSorts();
  for (const TypeNode& tn : dsorts)
  {
    toStreamModelSort(out, tn, m.getDomainElements(tn));
  }
  // print the declared terms
  const std::vector<Node>& dterms = m.getDeclaredTerms();
  for (const Node& n : dterms)
  {
    toStreamModelTerm(out, n, m.getValue(n));
  }
}

void Printer::toStream(std::ostream& out, const UnsatCore& core) const
{
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    toStreamCmdAssert(out, *i);
    out << std::endl;
  }
}/* Printer::toStream(UnsatCore) */

void Printer::toStream(std::ostream& out, const InstantiationList& is) const
{
  out << "(instantiations " << is.d_quant << std::endl;
  for (const InstantiationVec& i : is.d_inst)
  {
    out << "  ";
    if (i.d_id != theory::InferenceId::UNKNOWN)
    {
      out << "(! ";
    }
    out << "( ";
    for (const Node& n : i.d_vec)
    {
      out << n << " ";
    }
    out << ")";
    if (i.d_id != theory::InferenceId::UNKNOWN)
    {
      out << " :source " << i.d_id;
      if (!i.d_pfArg.isNull())
      {
        out << " " << i.d_pfArg;
      }
      out << ")";
    }
    out << std::endl;
  }
  out << ")" << std::endl;
}

void Printer::toStream(std::ostream& out, const SkolemList& sks) const
{
  out << "(skolem " << sks.d_quant << std::endl;
  out << "  ( ";
  for (const Node& n : sks.d_sks)
  {
    out << n << " ";
  }
  out << ")" << std::endl;
  out << ")" << std::endl;
}

Printer* Printer::getPrinter(std::ostream& out)
{
  Language lang = options::ioutils::getOutputLanguage(out);
  return getPrinter(lang);
}

Printer* Printer::getPrinter(Language lang)
{
  if (lang == Language::LANG_AUTO)
  {
    lang = Language::LANG_SMTLIB_V2_6;  // default
  }
  if (d_printers[static_cast<size_t>(lang)] == nullptr)
  {
    d_printers[static_cast<size_t>(lang)] = makePrinter(lang);
  }
  return d_printers[static_cast<size_t>(lang)].get();
}

void Printer::printUnknownCommandStatus(std::ostream& out,
                                        const std::string& name) const
{
  out << "ERROR: don't know how to print " << name << " command status"
      << std::endl;
}

void Printer::printUnknownCommand(std::ostream& out,
                                  const std::string& name) const
{
  out << "ERROR: don't know how to print " << name << " command" << std::endl;
}

void Printer::toStreamCmdSuccess(std::ostream& out) const
{
  printUnknownCommandStatus(out, "success");
}

void Printer::toStreamCmdInterrupted(std::ostream& out) const
{
  printUnknownCommandStatus(out, "interrupted");
}

void Printer::toStreamCmdUnsupported(std::ostream& out) const
{
  printUnknownCommandStatus(out, "unsupported");
}

void Printer::toStreamCmdFailure(std::ostream& out,
                                 const std::string& message) const
{
  printUnknownCommandStatus(out, "failure");
}

void Printer::toStreamCmdRecoverableFailure(std::ostream& out,
                                            const std::string& message) const
{
  printUnknownCommandStatus(out, "recoverable-failure");
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

void Printer::toStreamCmdPush(std::ostream& out, uint32_t nscopes) const
{
  printUnknownCommand(out, "push");
}

void Printer::toStreamCmdPop(std::ostream& out, uint32_t nscopes) const
{
  printUnknownCommand(out, "pop");
}

void Printer::toStreamCmdDeclareFunction(std::ostream& out,
                                         const std::string& id,
                                         TypeNode type) const
{
  printUnknownCommand(out, "declare-fun");
}

void Printer::toStreamCmdDeclareFunction(std::ostream& out, const Node& v) const
{
  // Must print the variable on the output stream (instead of just getting the
  // name of v), since this method may be called on variables that do not have
  // assigned names.
  std::stringstream ss;
  toStream(ss, v);
  toStreamCmdDeclareFunction(out, ss.str(), v.getType());
}

void Printer::toStreamCmdDeclarePool(std::ostream& out,
                                     const std::string& id,
                                     TypeNode type,
                                     const std::vector<Node>& initValue) const
{
  printUnknownCommand(out, "declare-pool");
}

void Printer::toStreamCmdDeclareOracleFun(std::ostream& out,
                                          const std::string& id,
                                          TypeNode type,
                                          const std::string& binName) const
{
  printUnknownCommand(out, "declare-oracle-fun");
}

void Printer::toStreamCmdDeclareType(std::ostream& out,
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

void Printer::toStreamCmdDefineFunction(std::ostream& out,
                                        Node v,
                                        Node lambda) const
{
  std::stringstream vs;
  vs << v;
  std::vector<Node> formals;
  Node body = lambda;
  TypeNode rangeType = v.getType();
  if (body.getKind() == kind::LAMBDA)
  {
    formals.insert(formals.end(), lambda[0].begin(), lambda[0].end());
    body = lambda[1];
    Assert(rangeType.isFunction());
    rangeType = rangeType.getRangeType();
  }
  toStreamCmdDefineFunction(out, vs.str(), formals, rangeType, body);
}

void Printer::toStreamCmdDefineFunctionRec(
    std::ostream& out,
    const std::vector<Node>& funcs,
    const std::vector<std::vector<Node>>& formals,
    const std::vector<Node>& formulas) const
{
  printUnknownCommand(out, "define-fun-rec");
}

void Printer::toStreamCmdDefineFunctionRec(
    std::ostream& out,
    const std::vector<Node>& funcs,
    const std::vector<Node>& lambdas) const
{
  std::vector<std::vector<Node>> formals;
  std::vector<Node> formulas;
  for (const Node& l : lambdas)
  {
    std::vector<Node> formalsVec;
    Node formula;
    if (l.getKind() == kind::LAMBDA)
    {
      formalsVec.insert(formalsVec.end(), l[0].begin(), l[0].end());
      formula = l[1];
    }
    else
    {
      formula = l;
    }
    formals.emplace_back(formalsVec);
    formulas.emplace_back(formula);
  }
  toStreamCmdDefineFunctionRec(out, funcs, formals, formulas);
}

void Printer::toStreamCmdSetUserAttribute(std::ostream& out,
                                          const std::string& attr,
                                          Node n) const
{
  printUnknownCommand(out, "set-user-attribute");
}

void Printer::toStreamCmdCheckSat(std::ostream& out) const
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
                                  const std::string& id,
                                  const std::vector<Node>& vars,
                                  TypeNode rangeType,
                                  TypeNode sygusType) const
{
  printUnknownCommand(out, "synth-fun");
}

void Printer::toStreamCmdConstraint(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "constraint");
}

void Printer::toStreamCmdAssume(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "assume");
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
void Printer::toStreamCmdCheckSynthNext(std::ostream& out) const
{
  printUnknownCommand(out, "check-synth-next");
}

void Printer::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  printUnknownCommand(out, "simplify");
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

void Printer::toStreamCmdBlockModel(std::ostream& out,
                                    modes::BlockModelsMode mode) const
{
  printUnknownCommand(out, "block-model");
}

void Printer::toStreamCmdBlockModelValues(std::ostream& out,
                                          const std::vector<Node>& nodes) const
{
  printUnknownCommand(out, "block-model-values");
}

void Printer::toStreamCmdGetProof(std::ostream& out,
                                  modes::ProofComponent c) const
{
  printUnknownCommand(out, "get-proof");
}

void Printer::toStreamCmdGetInstantiations(std::ostream& out) const
{
  printUnknownCommand(out, "get-instantiations");
}

void Printer::toStreamCmdGetInterpol(std::ostream& out,
                                     const std::string& name,
                                     Node conj,
                                     TypeNode sygusType) const
{
  printUnknownCommand(out, "get-interpolant");
}

void Printer::toStreamCmdGetInterpolNext(std::ostream& out) const
{
  printUnknownCommand(out, "get-interpolant-next");
}

void Printer::toStreamCmdGetAbduct(std::ostream& out,
                                   const std::string& name,
                                   Node conj,
                                   TypeNode sygusType) const
{
  printUnknownCommand(out, "get-abduct");
}

void Printer::toStreamCmdGetAbductNext(std::ostream& out) const
{
  printUnknownCommand(out, "get-abduct-next");
}

void Printer::toStreamCmdGetQuantifierElimination(std::ostream& out,
                                                  Node n,
                                                  bool doFull) const
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

void Printer::toStreamCmdGetDifficulty(std::ostream& out) const
{
  printUnknownCommand(out, "get-difficulty");
}

void Printer::toStreamCmdGetTimeoutCore(std::ostream& out) const
{
  printUnknownCommand(out, "get-timeout-core");
}

void Printer::toStreamCmdGetLearnedLiterals(std::ostream& out,
                                            modes::LearnedLitType t) const
{
  printUnknownCommand(out, "get-learned-literals");
}

void Printer::toStreamCmdGetAssertions(std::ostream& out) const
{
  printUnknownCommand(out, "get-assertions");
}

void Printer::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                           const std::string& logic) const
{
  printUnknownCommand(out, "set-logic");
}

void Printer::toStreamCmdSetInfo(std::ostream& out,
                                 const std::string& flag,
                                 const std::string& value) const
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
                                   const std::string& value) const
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

void Printer::toStreamCmdDeclareHeap(std::ostream& out,
                                     TypeNode locType,
                                     TypeNode dataType) const
{
  printUnknownCommand(out, "declare-heap");
}

}  // namespace cvc5::internal
