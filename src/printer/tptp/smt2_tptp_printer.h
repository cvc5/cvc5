/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for SMT2-derived TPTP output.
 */

#include "cvc5_private.h"

#ifndef CVC5__PRINTER__SMT2_TPTP_PRINTER_H
#define CVC5__PRINTER__SMT2_TPTP_PRINTER_H

#include <functional>
#include <string>

#include "printer/smt2/smt2_printer.h"
#include "smt/model.h"

namespace cvc5::internal {
namespace printer {
namespace smt2 {

/** TPTP input dialect, used when emitting model-verification annotations. */
enum class TptpDialect
{
  AUTO,
  CNF,
  FOF,
  TFF,
  THF,
};

/** Parse a lowercase dialect string ("cnf", "fof", "tff", "thf") into the
 *  corresponding TptpDialect enum value; returns AUTO for unknown strings. */
TptpDialect tptpDialectFromString(const std::string& input);

/**
 * A thin smt::Model subclass that carries the extra state needed by the TPTP
 * model printer: the input dialect, the model-verification flag, and a
 * fallback evaluator for closed terms not listed in the model declarations.
 *
 * Keeping these fields here avoids polluting the generic smt::Model with
 * TPTP-specific concerns.
 */
class TptpModel : public smt::Model
{
 public:
  TptpModel(bool isKnownSat,
            const std::string& inputName,
            bool tptpModelVerification = false,
            TptpDialect tptpInputDialect = TptpDialect::AUTO);

  /** Whether TPTP model output should preserve explicit input metadata. */
  bool useTptpModelVerification() const { return d_tptpModelVerification; }
  /** Input TPTP dialect supplied by the caller, when known. */
  TptpDialect getTptpInputDialect() const { return d_tptpInputDialect; }

  /** Return the model value of n, or a null node if it is not available. */
  Node getValueOrNull(TNode n) const;
  /** Evaluate a closed Boolean term; returns false if the value is unknown. */
  bool getBooleanValue(TNode n, bool& value) const;
  /** Register a fallback evaluator (e.g. TheoryModel::getValue). */
  void setEvaluator(const std::function<Node(TNode)>& eval);

 private:
  /** Whether model output should preserve explicit input metadata. */
  bool d_tptpModelVerification;
  /** Input TPTP dialect supplied by the caller (AUTO when not known). */
  TptpDialect d_tptpInputDialect;
  /** Optional fallback evaluator for closed terms (e.g. TheoryModel::getValue).
   */
  std::function<Node(TNode)> d_evaluator;
};

/**
 * Printer for SMT2-derived TPTP model output (language LANG_SMTLIB_V2_6_TPTP).
 */
class Smt2TptpPrinter : public Smt2Printer
{
 public:
  Smt2TptpPrinter() : Smt2Printer() {}
  using cvc5::internal::Printer::toStream;

  void toStream(std::ostream& out, const smt::Model& m) const override;
  void toStream(std::ostream& out, TNode n) const override;
  void toStream(std::ostream& out, Kind k) const override;

  void toStreamCmdAssert(std::ostream& out, Node n) const override;
  void toStreamCmdDeclareFunction(std::ostream& out,
                                  const std::string& id,
                                  const std::vector<TypeNode>& argTypes,
                                  TypeNode type) const override;
  void toStreamCmdCheckSat(std::ostream& out) const override;
};

}  // namespace smt2
}  // namespace printer
}  // namespace cvc5::internal

#endif /* CVC5__PRINTER__SMT2_TPTP_PRINTER_H */
