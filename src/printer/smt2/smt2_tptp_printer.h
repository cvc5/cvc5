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

#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {
namespace printer {
namespace smt2 {

/**
 * Base class for a custom SMT2 TPTP printer.
 *
 * This class currently delegates to Smt2Printer for all behavior. Override
 * command/node printing methods incrementally to implement the new format.
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
