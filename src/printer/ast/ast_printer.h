/*********************                                                        */
/*! \file ast_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the AST output language
 **
 ** The pretty-printer interface for the AST output language.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__AST_PRINTER_H
#define CVC4__PRINTER__AST_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace ast {

class AstPrinter : public CVC4::Printer
{
 public:
  using CVC4::Printer::toStream;
  void toStream(std::ostream& out,
                TNode n,
                int toDepth,
                bool types,
                size_t dag) const override;
  void toStream(std::ostream& out, const CommandStatus* s) const override;
  void toStream(std::ostream& out, const Model& m) const override;

  /** Print empty command */
  void toStreamCmdEmpty(std::ostream& out,
                        const std::string& name) const override;

  /** Print echo command */
  void toStreamCmdEcho(std::ostream& out,
                       const std::string& output) const override;

  /** Print assert command */
  void toStreamCmdAssert(std::ostream& out, Node n) const override;

  /** Print push command */
  void toStreamCmdPush(std::ostream& out) const override;

  /** Print pop command */
  void toStreamCmdPop(std::ostream& out) const override;

  /** Print declare-fun command */
  void toStreamCmdDeclareFunction(std::ostream& out,
                                  const std::string& id,
                                  TypeNode type) const override;

  /** Print declare-sort command */
  void toStreamCmdDeclareType(std::ostream& out,
                              const std::string& id,
                              size_t arity,
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

  /** Print define-named-fun command */
  void toStreamCmdDefineNamedFunction(std::ostream& out,
                                      const std::string& id,
                                      const std::vector<Node>& formals,
                                      TypeNode range,
                                      Node formula) const override;

  /** Print check-sat command */
  void toStreamCmdCheckSat(std::ostream& out,
                           Node n = Node::null()) const override;

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
  void toStreamCmdGetProof(std::ostream& out) const override;

  /** Print get-unsat-core command */
  void toStreamCmdGetUnsatCore(std::ostream& out) const override;

  /** Print get-assertions command */
  void toStreamCmdGetAssertions(std::ostream& out) const override;

  /** Print set-info :status command */
  void toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                     Result::Sat status) const override;

  /** Print set-logic command */
  void toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                    const std::string& logic) const override;

  /** Print set-info command */
  void toStreamCmdSetInfo(std::ostream& out,
                          const std::string& flag,
                          SExpr sexpr) const override;

  /** Print get-info command */
  void toStreamCmdGetInfo(std::ostream& out,
                          const std::string& flag) const override;

  /** Print set-option command */
  void toStreamCmdSetOption(std::ostream& out,
                            const std::string& flag,
                            SExpr sexpr) const override;

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

  /** Print comment command */
  void toStreamCmdComment(std::ostream& out,
                          const std::string& comment) const override;

  /** Print command sequence command */
  void toStreamCmdCommandSequence(
      std::ostream& out, const std::vector<Command*>& sequence) const override;

  /** Print declaration sequence command */
  void toStreamCmdDeclarationSequence(
      std::ostream& out, const std::vector<Command*>& sequence) const override;

 private:
  void toStream(std::ostream& out, TNode n, int toDepth, bool types) const;
  void toStream(std::ostream& out,
                const Model& m,
                const NodeCommand* c) const override;
}; /* class AstPrinter */

}  // namespace ast
}  // namespace printer
}  // namespace CVC4

#endif /* CVC4__PRINTER__AST_PRINTER_H */
