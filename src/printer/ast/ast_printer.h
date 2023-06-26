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
 * The pretty-printer interface for the AST output language.
 */

#include "cvc5_private.h"

#ifndef CVC5__PRINTER__AST_PRINTER_H
#define CVC5__PRINTER__AST_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace cvc5::internal {

class LetBinding;

namespace printer {
namespace ast {

class AstPrinter : public cvc5::internal::Printer
{
 public:
  using cvc5::internal::Printer::toStream;
  void toStream(std::ostream& out, TNode n) const override;
  void toStream(std::ostream& out, Kind k) const override;
  void toStream(std::ostream& out, const smt::Model& m) const override;

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

  /** Print declare-sort command */
  void toStreamCmdDeclareType(std::ostream& out,
                              TypeNode type) const override;

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

  /** Print check-sat command */
  void toStreamCmdCheckSat(std::ostream& out) const override;

  /** Print check-sat-assuming command */
  void toStreamCmdCheckSatAssuming(
      std::ostream& out, const std::vector<Node>& nodes) const override;

  /** Print query command */
  void toStreamCmdQuery(std::ostream& out, Node n) const override;

  /** Print simplify command */
  void toStreamCmdSimplify(std::ostream& out, Node nodes) const override;

  /** Print get-value command */
  void toStreamCmdGetValue(std::ostream& out,
                           const std::vector<Node>& n) const override;

  /** Print get-assignment command */
  void toStreamCmdGetAssignment(std::ostream& out) const override;

  /** Print get-model command */
  void toStreamCmdGetModel(std::ostream& out) const override;

  /** Print get-proof command */
  void toStreamCmdGetProof(std::ostream& out,
                           modes::ProofComponent c) const override;

  /** Print get-unsat-core command */
  void toStreamCmdGetUnsatCore(std::ostream& out) const override;

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

 private:
  void toStream(std::ostream& out,
                TNode n,
                int toDepth,
                LetBinding* lbind = nullptr) const;
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
}; /* class AstPrinter */

}  // namespace ast
}  // namespace printer
}  // namespace cvc5::internal

#endif /* CVC5__PRINTER__AST_PRINTER_H */
