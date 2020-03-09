/*********************                                                        */
/*! \file cvc_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the CVC output language
 **
 ** The pretty-printer interface for the CVC output language.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__CVC_PRINTER_H
#define CVC4__PRINTER__CVC_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace cvc {

class CvcPrinter : public CVC4::Printer {
 public:
  using CVC4::Printer::toStream;
  CvcPrinter(bool cvc3Mode = false) : d_cvc3Mode(cvc3Mode) { }
  void toStream(std::ostream& out,
                TNode n,
                int toDepth,
                bool types,
                size_t dag) const override;
  void toStream(std::ostream& out,
                const Command* c,
                int toDepth,
                bool types,
                size_t dag) const override;
  void toStream(std::ostream& out, const CommandStatus* s) const override;
  void toStream(std::ostream& out, const Model& m) const override;

 private:
  void toStream(
      std::ostream& out, TNode n, int toDepth, bool types, bool bracket) const;
  void toStream(std::ostream& out,
                const Model& m,
                const Command* c) const override;

  bool d_cvc3Mode;
};/* class CvcPrinter */

}/* CVC4::printer::cvc namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* CVC4__PRINTER__CVC_PRINTER_H */
