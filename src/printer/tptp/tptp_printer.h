/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the TPTP output language.
 */

#include "cvc5_private.h"

#ifndef CVC5__PRINTER__TPTP_PRINTER_H
#define CVC5__PRINTER__TPTP_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace cvc5 {
namespace printer {
namespace tptp {

class TptpPrinter : public cvc5::Printer
{
 public:
  using cvc5::Printer::toStream;
  void toStream(std::ostream& out,
                TNode n,
                int toDepth,
                size_t dag) const override;
  void toStream(std::ostream& out, const CommandStatus* s) const override;
  void toStream(std::ostream& out, const smt::Model& m) const override;
  /** print unsat core to stream
   * We use the expression names stored in the SMT engine associated with the
   * unsat core with UnsatCore::getSmtEngine.
   */
  void toStream(std::ostream& out, const UnsatCore& core) const override;

 private:
  /**
   * To stream model sort. This prints the appropriate output for type
   * tn declared via declare-sort or declare-datatype.
   */
  void toStreamModelSort(std::ostream& out,
                         const smt::Model& m,
                         TypeNode tn) const override;

  /**
   * To stream model term. This prints the appropriate output for term
   * n declared via declare-fun.
   */
  void toStreamModelTerm(std::ostream& out,
                         const smt::Model& m,
                         Node n) const override;

}; /* class TptpPrinter */

}  // namespace tptp
}  // namespace printer
}  // namespace cvc5

#endif /* CVC5__PRINTER__TPTP_PRINTER_H */
