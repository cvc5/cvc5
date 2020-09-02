/*********************                                                        */
/*! \file printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Aina Niemetz
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

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__PRINTER_H
#define CVC4__PRINTER__PRINTER_H

#include <map>
#include <string>

#include "expr/node.h"
#include "options/language.h"
#include "smt/command.h"
#include "smt/model.h"
#include "util/sexpr.h"

namespace CVC4 {

class NodeCommand;

class Printer
{
 public:
  /**
   * Since the printers are managed as unique_ptr, we need public acces to
   * the virtual destructor.
   */
  virtual ~Printer() {}

  /** Get the Printer for a given OutputLanguage */
  static Printer* getPrinter(OutputLanguage lang);

  /** Write a Node out to a stream with this Printer. */
  virtual void toStream(std::ostream& out,
                        TNode n,
                        int toDepth,
                        bool types,
                        size_t dag) const = 0;

  /** Write a CommandStatus out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const CommandStatus* s) const = 0;

  /** Write a Model out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Model& m) const;

  /** Write an UnsatCore out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const UnsatCore& core) const;

  /** Print empty command */
  virtual void toStreamCmdEmpty(std::ostream& out,
                                const std::string& name) const;

  /** Print echo command */
  virtual void toStreamCmdEcho(std::ostream& out,
                               const std::string& output) const;

  /** Print assert command */
  virtual void toStreamCmdAssert(std::ostream& out, Node n) const;

  /** Print push command */
  virtual void toStreamCmdPush(std::ostream& out) const;

  /** Print pop command */
  virtual void toStreamCmdPop(std::ostream& out) const;

  /** Print declare-fun command */
  virtual void toStreamCmdDeclareFunction(std::ostream& out,
                                          const std::string& id,
                                          TypeNode type) const;

  /** Print declare-sort command */
  virtual void toStreamCmdDeclareType(std::ostream& out,
                                      const std::string& id,
                                      size_t arity,
                                      TypeNode type) const;

  /** Print define-sort command */
  virtual void toStreamCmdDefineType(std::ostream& out,
                                     const std::string& id,
                                     const std::vector<TypeNode>& params,
                                     TypeNode t) const;

  /** Print define-fun command */
  virtual void toStreamCmdDefineFunction(std::ostream& out,
                                         const std::string& id,
                                         const std::vector<Node>& formals,
                                         TypeNode range,
                                         Node formula) const;

  /** Print define-named-fun command */
  virtual void toStreamCmdDefineNamedFunction(std::ostream& out,
                                              const std::string& id,
                                              const std::vector<Node>& formals,
                                              TypeNode range,
                                              Node formula) const;

  /** Print define-fun-rec command */
  virtual void toStreamCmdDefineFunctionRec(
      std::ostream& out,
      const std::vector<Node>& funcs,
      const std::vector<std::vector<Node>>& formals,
      const std::vector<Node>& formulas) const;

  /** Print set-user-attribute command */
  void toStreamCmdSetUserAttribute(std::ostream& out,
                                   const std::string& attr,
                                   Node n) const;

  /** Print check-sat command */
  virtual void toStreamCmdCheckSat(std::ostream& out,
                                   Node n = Node::null()) const;

  /** Print check-sat-assuming command */
  virtual void toStreamCmdCheckSatAssuming(
      std::ostream& out, const std::vector<Node>& nodes) const;

  /** Print query command */
  virtual void toStreamCmdQuery(std::ostream& out, Node n) const;

  /** Print declare-var command */
  virtual void toStreamCmdDeclareVar(std::ostream& out,
                                     Node var,
                                     TypeNode type) const;

  /** Print synth-fun command */
  virtual void toStreamCmdSynthFun(std::ostream& out,
                                   const std::string& sym,
                                   const std::vector<Node>& vars,
                                   TypeNode range,
                                   bool isInv,
                                   TypeNode sygusType) const;

  /** Print constraint command */
  virtual void toStreamCmdConstraint(std::ostream& out, Node n) const;

  /** Print inv-constraint command */
  virtual void toStreamCmdInvConstraint(
      std::ostream& out, Node inv, Node pre, Node trans, Node post) const;

  /** Print check-synth command */
  virtual void toStreamCmdCheckSynth(std::ostream& out) const;

  /** Print simplify command */
  virtual void toStreamCmdSimplify(std::ostream& out, Node n) const;

  /** Print expand-definitions command */
  void toStreamCmdExpandDefinitions(std::ostream& out, Node n) const;

  /** Print get-value command */
  virtual void toStreamCmdGetValue(std::ostream& out,
                                   const std::vector<Node>& nodes) const;

  /** Print get-assignment command */
  virtual void toStreamCmdGetAssignment(std::ostream& out) const;

  /** Print get-model command */
  virtual void toStreamCmdGetModel(std::ostream& out) const;

  /** Print block-model command */
  void toStreamCmdBlockModel(std::ostream& out) const;

  /** Print block-model-values command */
  void toStreamCmdBlockModelValues(std::ostream& out,
                                   const std::vector<Node>& nodes) const;

  /** Print get-proof command */
  virtual void toStreamCmdGetProof(std::ostream& out) const;

  /** Print get-instantiations command */
  void toStreamCmdGetInstantiations(std::ostream& out) const;

  /** Print get-synth-solution command */
  void toStreamCmdGetSynthSolution(std::ostream& out) const;

  /** Print get-interpol command */
  void toStreamCmdGetInterpol(std::ostream& out,
                              const std::string& name,
                              Node conj,
                              TypeNode sygusType) const;

  /** Print get-abduct command */
  virtual void toStreamCmdGetAbduct(std::ostream& out,
                                    const std::string& name,
                                    Node conj,
                                    TypeNode sygusType) const;

  /** Print get-quantifier-elimination command */
  void toStreamCmdGetQuantifierElimination(std::ostream& out, Node n) const;

  /** Print get-unsat-assumptions command */
  virtual void toStreamCmdGetUnsatAssumptions(std::ostream& out) const;

  /** Print get-unsat-core command */
  virtual void toStreamCmdGetUnsatCore(std::ostream& out) const;

  /** Print get-assertions command */
  virtual void toStreamCmdGetAssertions(std::ostream& out) const;

  /** Print set-info :status command */
  virtual void toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                             BenchmarkStatus status) const;

  /** Print set-logic command */
  virtual void toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                            const std::string& logic) const;

  /** Print set-info command */
  virtual void toStreamCmdSetInfo(std::ostream& out,
                                  const std::string& flag,
                                  SExpr sexpr) const;

  /** Print get-info command */
  virtual void toStreamCmdGetInfo(std::ostream& out,
                                  const std::string& flag) const;

  /** Print set-option command */
  virtual void toStreamCmdSetOption(std::ostream& out,
                                    const std::string& flag,
                                    SExpr sexpr) const;

  /** Print get-option command */
  virtual void toStreamCmdGetOption(std::ostream& out,
                                    const std::string& flag) const;

  /** Print set-expression-name command */
  void toStreamCmdSetExpressionName(std::ostream& out,
                                    Node n,
                                    const std::string& name) const;

  /** Print declare-datatype(s) command */
  virtual void toStreamCmdDatatypeDeclaration(
      std::ostream& out, const std::vector<TypeNode>& datatypes) const;

  /** Print reset command */
  virtual void toStreamCmdReset(std::ostream& out) const;

  /** Print reset-assertions command */
  virtual void toStreamCmdResetAssertions(std::ostream& out) const;

  /** Print quit command */
  virtual void toStreamCmdQuit(std::ostream& out) const;

  /** Print comment command */
  virtual void toStreamCmdComment(std::ostream& out,
                                  const std::string& comment) const;

  /** Print command sequence command */
  virtual void toStreamCmdCommandSequence(
      std::ostream& out, const std::vector<Command*>& sequence) const;

  /** Print declaration sequence command */
  virtual void toStreamCmdDeclarationSequence(
      std::ostream& out, const std::vector<Command*>& sequence) const;

 protected:
  /** Derived classes can construct, but no one else. */
  Printer() {}

  /** write model response to command */
  virtual void toStream(std::ostream& out,
                        const Model& m,
                        const NodeCommand* c) const = 0;

  /** write model response to command using another language printer */
  void toStreamUsing(OutputLanguage lang,
                     std::ostream& out,
                     const Model& m,
                     const NodeCommand* c) const
  {
    getPrinter(lang)->toStream(out, m, c);
  }

  /**
   * Write an error to `out` stating that command `name` is not supported by
   * this printer.
   */
  void printUnknownCommand(std::ostream& out, const std::string& name) const;

 private:
  /** Disallow copy, assignment  */
  Printer(const Printer&) = delete;
  Printer& operator=(const Printer&) = delete;

  /** Make a Printer for a given OutputLanguage */
  static std::unique_ptr<Printer> makePrinter(OutputLanguage lang);

  /** Printers for each OutputLanguage */
  static std::unique_ptr<Printer> d_printers[language::output::LANG_MAX];

}; /* class Printer */

}  // namespace CVC4

#endif /* CVC4__PRINTER__PRINTER_H */
