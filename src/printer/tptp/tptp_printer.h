/*********************                                                        */
/*! \file tptp_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the TPTP output language
 **
 ** The pretty-printer interface for the TPTP output language.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__TPTP_PRINTER_H
#define CVC4__PRINTER__TPTP_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace tptp {

class TptpPrinter : public CVC4::Printer
{
 public:
  using CVC4::Printer::toStream;
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
}  // namespace CVC4

#endif /* CVC4__PRINTER__TPTP_PRINTER_H */
