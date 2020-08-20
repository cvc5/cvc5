/*********************                                                        */
/*! \file tptp_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
                bool types,
                size_t dag) const override;
  void toStream(std::ostream& out, const CommandStatus* s) const override;
  void toStream(std::ostream& out, const Model& m) const override;
  /** print unsat core to stream
   * We use the expression names stored in the SMT engine associated with the
   * unsat core with UnsatCore::getSmtEngine.
   */
  void toStream(std::ostream& out, const UnsatCore& core) const override;

 private:
  void toStream(std::ostream& out,
                const Model& m,
                const Command* c) const override;

}; /* class TptpPrinter */

}  // namespace tptp
}  // namespace printer
}  // namespace CVC4

#endif /* CVC4__PRINTER__TPTP_PRINTER_H */
