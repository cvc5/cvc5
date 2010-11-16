/*********************                                                        */
/*! \file smt2_printer.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the SMT2 output language
 **
 ** The pretty-printer interface for the SMT2 output language.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__SMT2_PRINTER_H
#define __CVC4__PRINTER__SMT2_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace smt2 {

class Smt2Printer : public CVC4::Printer {
public:
  void toStream(std::ostream& out, TNode n, int toDepth, bool types) const;
};/* class Smt2Printer */

}/* CVC4::printer::smt2 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__SMT2_PRINTER_H */

