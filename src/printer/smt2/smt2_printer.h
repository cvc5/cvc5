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
 * The pretty-printer interface for the SMT2 output language.
 */

#include "cvc5_private.h"

#ifndef CVC5__PRINTER__SMT2_PRINTER_H
#define CVC5__PRINTER__SMT2_PRINTER_H

#include "printer/printer.h"

namespace cvc5::internal {

class LetBinding;
class DType;

namespace printer {
namespace smt2 {

enum Variant
{
  no_variant,
  smt2_6_variant,  // new-style 2.6 syntax, when it makes a difference, with
                   // support for the string standard
};                 /* enum Variant */

class Smt2Printer : public cvc5::internal::Printer
{
 public:
  Smt2Printer(Variant variant = no_variant) : d_variant(variant) {}
  using cvc5::internal::Printer::toStream;
  void toStream(std::ostream& out, TNode n) const override;
  void toStream(std::ostream& out, TNode n, int toDepth, size_t dag) const;
  void toStream(std::ostream& out, Kind k) const override;
  void toStream(std::ostream& out, const smt::Model& m) const override;
  /**
   * Writes the unsat core to the stream out.
   * We use the expression names that are associated with the core
   * (UnsatCore::getCoreNames) for printing named assertions.
   */
  void toStream(std::ostream& out, const UnsatCore& core) const override;

  void toStreamCmdSuccess(std::ostream& out) const override;
  void toStreamCmdInterrupted(std::ostream& out) const override;
  void toStreamCmdUnsupported(std::ostream& out) const override;
  void toStreamCmdFailure(std::ostream& out,
                          const std::string& message) const override;
  void toStreamCmdRecoverableFailure(std::ostream& out,
                                     const std::string& message) const override;

  /** Print empty command */
  void toStreamCmdEmpty(std::ostream& out,
                        const std::string& name) const override;

  /** Print echo command */
  void toStreamCmdEcho(std::ostream& out,
                       const std::string& output) const override;

  /** Print assert command */
  void toStreamCmdAssert(std::ostream& out, Node n) const override;

  /** Print push command */
  void toStreamCmdPush(std::ostream& out, uint32_t nscopes) const override;

  /** Print pop command */
  void toStreamCmdPop(std::ostream& out, uint32_t nscopes) const override;

  /** Print declare-fun command */
  void toStreamCmdDeclareFunction(std::ostream& out,
                                  const std::string& id,
                                  TypeNode type) const override;

  /** Print declare-oracle-fun command */
  void toStreamCmdDeclareOracleFun(std::ostream& out,
                                   const std::string& id,
                                   TypeNode type,
                                   const std::string& binName) const override;

  /** Print declare-pool command */
  void toStreamCmdDeclarePool(std::ostream& out,
                                      const std::string& id,
                                      TypeNode type,
                                      const std::vector<Node>& initValue) const override;

  /** Print declare-sort command */
  void toStreamCmdDeclareType(std::ostream& out, TypeNode type) const override;

  /** Print define-sort command */
  void toStreamCmdDefineType(std::ostream& out,
                             const std::string& id,
                             const std::vector<TypeNode>& params,
                             TypeNode t) const override;

  /** Print define-fun command */
  void toStreamCmdDefineFunction(std::ostream& out,
                                 const std::string& id,
                                 const std::vector<Node>& formals,
                                 TypeNode range,
                                 Node formula) const override;

  /** Print define-fun-rec command */
  void toStreamCmdDefineFunctionRec(
      std::ostream& out,
      const std::vector<Node>& funcs,
      const std::vector<std::vector<Node>>& formals,
      const std::vector<Node>& formulas) const override;

  /** Print check-sat command */
  void toStreamCmdCheckSat(std::ostream& out) const override;

  /** Print check-sat-assuming command */
  void toStreamCmdCheckSatAssuming(
      std::ostream& out, const std::vector<Node>& nodes) const override;

  /** Print query command */
  void toStreamCmdQuery(std::ostream& out, Node n) const override;

  /** Print declare-var command */
  void toStreamCmdDeclareVar(std::ostream& out,
                             Node var,
                             TypeNode type) const override;

  /** Print synth-fun command */
  void toStreamCmdSynthFun(
      std::ostream& out,
      const std::string& id,
      const std::vector<Node>& vars,
      TypeNode rangeType,
      TypeNode sygusType) const override;

  /** Print constraint command */
  void toStreamCmdConstraint(std::ostream& out, Node n) const override;

  /** Print assume command */
  void toStreamCmdAssume(std::ostream& out, Node n) const override;

  /** Print inv-constraint command */
  void toStreamCmdInvConstraint(std::ostream& out,
                                Node inv,
                                Node pre,
                                Node trans,
                                Node post) const override;

  /** Print check-synth command */
  void toStreamCmdCheckSynth(std::ostream& out) const override;

  /** Print check-synth-next command */
  void toStreamCmdCheckSynthNext(std::ostream& out) const override;

  /** Print simplify command */
  void toStreamCmdSimplify(std::ostream& out, Node nodes) const override;

  /** Print get-value command */
  void toStreamCmdGetValue(std::ostream& out,
                           const std::vector<Node>& n) const override;

  /** Print get-assignment command */
  void toStreamCmdGetAssignment(std::ostream& out) const override;

  /** Print get-model command */
  void toStreamCmdGetModel(std::ostream& out) const override;

  /** Print block-model command */
  void toStreamCmdBlockModel(std::ostream& out,
                             modes::BlockModelsMode mode) const override;

  /** Print block-model-values command */
  void toStreamCmdBlockModelValues(
      std::ostream& out, const std::vector<Node>& nodes) const override;

  /** Print get-proof command */
  void toStreamCmdGetProof(std::ostream& out,
                           modes::ProofComponent c) const override;

  /** Print get-interpolant command */
  void toStreamCmdGetInterpol(std::ostream& out,
                              const std::string& name,
                              Node conj,
                              TypeNode sygusType) const override;

  /** Print get-interpolant-next command */
  void toStreamCmdGetInterpolNext(std::ostream& out) const override;

  /** Print get-abduct command */
  void toStreamCmdGetAbduct(std::ostream& out,
                            const std::string& name,
                            Node conj,
                            TypeNode sygusType) const override;

  /** Print get-abduct-next command */
  void toStreamCmdGetAbductNext(std::ostream& out) const override;

  /** Print get-quantifier-elimination command */
  void toStreamCmdGetQuantifierElimination(std::ostream& out,
                                           Node n,
                                           bool doFull) const override;

  /** Print get-unsat-assumptions command */
  void toStreamCmdGetUnsatAssumptions(std::ostream& out) const override;

  /** Print get-unsat-core command */
  void toStreamCmdGetUnsatCore(std::ostream& out) const override;

  /** Print get-difficulty command */
  void toStreamCmdGetDifficulty(std::ostream& out) const override;

  /** Print get-timeout-core command */
  void toStreamCmdGetTimeoutCore(std::ostream& out) const override;

  /** Print get-learned-literals command */
  void toStreamCmdGetLearnedLiterals(std::ostream& out,
                                     modes::LearnedLitType t) const override;

  /** Print get-assertions command */
  void toStreamCmdGetAssertions(std::ostream& out) const override;

  /** Print set-logic command */
  void toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                    const std::string& logic) const override;

  /** Print set-info command */
  void toStreamCmdSetInfo(std::ostream& out,
                          const std::string& flag,
                          const std::string& value) const override;

  /** Print get-info command */
  void toStreamCmdGetInfo(std::ostream& out,
                          const std::string& flag) const override;

  /** Print set-option command */
  void toStreamCmdSetOption(std::ostream& out,
                            const std::string& flag,
                            const std::string& value) const override;

  /** Print get-option command */
  void toStreamCmdGetOption(std::ostream& out,
                            const std::string& flag) const override;

  /** Print declare-datatype(s) command */
  void toStreamCmdDatatypeDeclaration(
      std::ostream& out, const std::vector<TypeNode>& datatypes) const override;

  /** Print reset command */
  void toStreamCmdReset(std::ostream& out) const override;

  /** Print reset-assertions command */
  void toStreamCmdResetAssertions(std::ostream& out) const override;

  /** Print quit command */
  void toStreamCmdQuit(std::ostream& out) const override;

  /** Print declare-heap command */
  void toStreamCmdDeclareHeap(std::ostream& out,
                              TypeNode locType,
                              TypeNode dataType) const override;

  /**
   * Get the string for a kind k, which returns how the kind k is printed in
   * the SMT-LIB format.
   */
  static std::string smtKindString(Kind k);
  /**
   * Same as above, but also takes into account the type of the node, which
   * makes a difference for printing sequences.
   */
  static std::string smtKindStringOf(const Node& n);
  /**
   * Get the string corresponding to the sygus datatype t printed as a grammar.
   */
  static std::string sygusGrammarString(const TypeNode& t);

 private:
  /**
   * The main printing method for nodes n.
   */
  void toStream(std::ostream& out,
                TNode n,
                int toDepth,
                LetBinding* lbind = nullptr) const;
  /**
   * Prints the vector as a sorted variable list
   */
  void toStreamSortedVarList(std::ostream& out,
                             const std::vector<Node>& vars) const;
  /**
   * Prints a type as part of e.g. a declare-fun command. This prints either
   * `() T` if the type T is not a function, or `(T1 ... Tn) Tr` if T is
   * a function type with argument types T1 ... Tn and return Tr.
   */
  void toStreamDeclareType(std::ostream& out, TypeNode tn) const;
  /** To stream type node, which ensures tn is printed in smt2 format */
  void toStreamType(std::ostream& out, TypeNode tn) const;
  /** To stream datatype */
  void toStream(std::ostream& out, const DType& dt) const;
  /**
   * To stream model sort. This prints the appropriate output for type
   * tn declared via declare-sort or declare-datatype.
   */
  void toStreamModelSort(std::ostream& out,
                         TypeNode tn,
                         const std::vector<Node>& elements) const override;

  /**
   * To stream model term. This prints the appropriate output for term
   * n declared via declare-fun.
   */
  void toStreamModelTerm(std::ostream& out,
                         const Node& n,
                         const Node& value) const override;

  /**
   * To stream with let binding. This prints n, possibly in the scope
   * of letification generated by this method based on lbind.
   */
  void toStreamWithLetify(std::ostream& out,
                          Node n,
                          int toDepth,
                          LetBinding* lbind) const;
  Variant d_variant;
}; /* class Smt2Printer */

}  // namespace smt2
}  // namespace printer
}  // namespace cvc5::internal

#endif /* CVC5__PRINTER__SMT2_PRINTER_H */
