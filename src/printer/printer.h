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

#include "cvc5_private.h"

#ifndef CVC5__PRINTER__PRINTER_H
#define CVC5__PRINTER__PRINTER_H

#include <cvc5/cvc5_export.h>

#include <memory>
#include <string>
#include <vector>

#include "expr/kind.h"
#include "options/language.h"
#include "util/result.h"

namespace cvc5::internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;
class TypeNode;
class UnsatCore;
struct InstantiationList;
struct SkolemList;

namespace smt {
class Model;
}

class CVC5_EXPORT Printer
{
 public:
  /**
   * Since the printers are managed as unique_ptr, we need public acces to
   * the virtual destructor.
   */
  virtual ~Printer() {}

  /** Get the Printer for a given output stream */
  static Printer* getPrinter(std::ostream& out);

  /** Get the Printer for a given Language */
  static Printer* getPrinter(Language lang);

  /** Write a Node out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, TNode n) const = 0;

  /** Write a Kind out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, Kind k) const = 0;

  /** Write a Model out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const smt::Model& m) const;

  /** Write an UnsatCore out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const UnsatCore& core) const;

  /** Write an instantiation list out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const InstantiationList& is) const;

  /** Write a skolem list out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const SkolemList& sks) const;

  /** Print command success status */
  virtual void toStreamCmdSuccess(std::ostream& out) const;

  /** Print command interrupted status */
  virtual void toStreamCmdInterrupted(std::ostream& out) const;

  /** Print command unsupported status */
  virtual void toStreamCmdUnsupported(std::ostream& out) const;

  /** Print command failure status */
  virtual void toStreamCmdFailure(std::ostream& out,
                                  const std::string& message) const;

  /** Print command recoverable failure status */
  virtual void toStreamCmdRecoverableFailure(std::ostream& out,
                                             const std::string& message) const;

  /** Print empty command */
  virtual void toStreamCmdEmpty(std::ostream& out,
                                const std::string& name) const;

  /** Print echo command */
  virtual void toStreamCmdEcho(std::ostream& out,
                               const std::string& output) const;

  /** Print assert command */
  virtual void toStreamCmdAssert(std::ostream& out, Node n) const;

  /** Print push command */
  virtual void toStreamCmdPush(std::ostream& out, uint32_t nscopes) const;

  /** Print pop command */
  virtual void toStreamCmdPop(std::ostream& out, uint32_t nscopes) const;

  /** Print declare-fun command */
  virtual void toStreamCmdDeclareFunction(std::ostream& out,
                                          const std::string& id,
                                          TypeNode type) const;
  /** Variant of above for a pre-existing variable */
  void toStreamCmdDeclareFunction(std::ostream& out, const Node& v) const;
  /** Print declare-pool command */
  virtual void toStreamCmdDeclarePool(std::ostream& out,
                                      const std::string& id,
                                      TypeNode type,
                                      const std::vector<Node>& initValue) const;
  /** Print declare-oracle-fun command */
  virtual void toStreamCmdDeclareOracleFun(std::ostream& out,
                                           const std::string& id,
                                           TypeNode type,
                                           const std::string& binName) const;

  /** Print declare-sort command */
  virtual void toStreamCmdDeclareType(std::ostream& out,
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
  /** Variant of above that takes the definition */
  void toStreamCmdDefineFunction(std::ostream& out, Node v, Node lambda) const;

  /** Print define-fun-rec command */
  virtual void toStreamCmdDefineFunctionRec(
      std::ostream& out,
      const std::vector<Node>& funcs,
      const std::vector<std::vector<Node>>& formals,
      const std::vector<Node>& formulas) const;
  /** Variant of above that takes the definition */
  void toStreamCmdDefineFunctionRec(std::ostream& out,
                                    const std::vector<Node>& funcs,
                                    const std::vector<Node>& lambdas) const;

  /** Print set-user-attribute command */
  void toStreamCmdSetUserAttribute(std::ostream& out,
                                   const std::string& attr,
                                   Node n) const;

  /** Print check-sat command */
  virtual void toStreamCmdCheckSat(std::ostream& out) const;

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
                                   const std::string& id,
                                   const std::vector<Node>& vars,
                                   TypeNode rangeType,
                                   TypeNode sygusType) const;

  /** Print constraint command */
  virtual void toStreamCmdConstraint(std::ostream& out, Node n) const;

  /** Print assume command */
  virtual void toStreamCmdAssume(std::ostream& out, Node n) const;

  /** Print inv-constraint command */
  virtual void toStreamCmdInvConstraint(
      std::ostream& out, Node inv, Node pre, Node trans, Node post) const;

  /** Print check-synth command */
  virtual void toStreamCmdCheckSynth(std::ostream& out) const;

  /** Print check-synth-next command */
  virtual void toStreamCmdCheckSynthNext(std::ostream& out) const;

  /** Print simplify command */
  virtual void toStreamCmdSimplify(std::ostream& out, Node n) const;

  /** Print get-value command */
  virtual void toStreamCmdGetValue(std::ostream& out,
                                   const std::vector<Node>& nodes) const;

  /** Print get-assignment command */
  virtual void toStreamCmdGetAssignment(std::ostream& out) const;

  /** Print get-model command */
  virtual void toStreamCmdGetModel(std::ostream& out) const;

  /** Print block-model command */
  virtual void toStreamCmdBlockModel(std::ostream& out,
                                     modes::BlockModelsMode mode) const;

  /** Print block-model-values command */
  virtual void toStreamCmdBlockModelValues(
      std::ostream& out, const std::vector<Node>& nodes) const;

  /** Print get-proof command */
  virtual void toStreamCmdGetProof(std::ostream& out,
                                   modes::ProofComponent c) const;

  /** Print get-instantiations command */
  void toStreamCmdGetInstantiations(std::ostream& out) const;

  /** Print get-interpolant command */
  virtual void toStreamCmdGetInterpol(std::ostream& out,
                                      const std::string& name,
                                      Node conj,
                                      TypeNode sygusType) const;

  /** Print get-interpolant-next command */
  virtual void toStreamCmdGetInterpolNext(std::ostream& out) const;

  /** Print get-abduct command */
  virtual void toStreamCmdGetAbduct(std::ostream& out,
                                    const std::string& name,
                                    Node conj,
                                    TypeNode sygusType) const;

  /** Print get-abduct-next command */
  virtual void toStreamCmdGetAbductNext(std::ostream& out) const;

  /** Print get-quantifier-elimination command */
  virtual void toStreamCmdGetQuantifierElimination(std::ostream& out,
                                                   Node n,
                                                   bool doFull) const;

  /** Print get-unsat-assumptions command */
  virtual void toStreamCmdGetUnsatAssumptions(std::ostream& out) const;

  /** Print get-unsat-core command */
  virtual void toStreamCmdGetUnsatCore(std::ostream& out) const;

  /** Print get-difficulty command */
  virtual void toStreamCmdGetDifficulty(std::ostream& out) const;

  /** Print get-timeout-core command */
  virtual void toStreamCmdGetTimeoutCore(std::ostream& out) const;

  /** Print get-learned-literals command */
  virtual void toStreamCmdGetLearnedLiterals(std::ostream& out,
                                             modes::LearnedLitType t) const;

  /** Print get-assertions command */
  virtual void toStreamCmdGetAssertions(std::ostream& out) const;

  /** Print set-logic command */
  virtual void toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                            const std::string& logic) const;

  /** Print set-info command */
  virtual void toStreamCmdSetInfo(std::ostream& out,
                                  const std::string& flag,
                                  const std::string& value) const;

  /** Print get-info command */
  virtual void toStreamCmdGetInfo(std::ostream& out,
                                  const std::string& flag) const;

  /** Print set-option command */
  virtual void toStreamCmdSetOption(std::ostream& out,
                                    const std::string& flag,
                                    const std::string& value) const;

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

  /** Declare heap command */
  virtual void toStreamCmdDeclareHeap(std::ostream& out,
                                      TypeNode locType,
                                      TypeNode dataType) const;

 protected:
  /** Derived classes can construct, but no one else. */
  Printer() {}

  /**
   * To stream model sort. This prints the appropriate output for type
   * tn declared via declare-sort.
   */
  virtual void toStreamModelSort(std::ostream& out,
                                 TypeNode tn,
                                 const std::vector<Node>& elements) const = 0;

  /**
   * To stream model term. This prints the appropriate output for term
   * n declared via declare-fun.
   */
  virtual void toStreamModelTerm(std::ostream& out,
                                 const Node& n,
                                 const Node& value) const = 0;

  /**
   * Write an error to `out` stating that command status `name` is not supported
   * by this printer.
   */
  void printUnknownCommandStatus(std::ostream& out,
                                 const std::string& name) const;

  /**
   * Write an error to `out` stating that command `name` is not supported by
   * this printer.
   */
  void printUnknownCommand(std::ostream& out, const std::string& name) const;

 private:
  /** Disallow copy, assignment  */
  Printer(const Printer&) = delete;
  Printer& operator=(const Printer&) = delete;

  /** Make a Printer for a given Language */
  static std::unique_ptr<Printer> makePrinter(Language lang);

  /** Printers for each Language */
  static std::unique_ptr<Printer>
      d_printers[static_cast<size_t>(Language::LANG_MAX)];

}; /* class Printer */

}  // namespace cvc5::internal

#endif /* CVC5__PRINTER__PRINTER_H */
