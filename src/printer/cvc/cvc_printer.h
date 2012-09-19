/*********************                                                        */
/*! \file cvc_printer.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the CVC output language
 **
 ** The pretty-printer interface for the CVC output language.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__CVC_PRINTER_H
#define __CVC4__PRINTER__CVC_PRINTER_H

#include <iostream>

#include "printer/printer.h"
#include "printer/dagification_visitor.h"
#include "theory/substitutions.h"
#include "util/node_visitor.h"

namespace CVC4 {
namespace printer {
namespace cvc {

class CvcPrinter : public CVC4::Printer {
  void toStream(std::ostream& out, TNode n, int toDepth, bool types, bool bracket) const throw();
public:
  void toStream(std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const throw();
  void toStream(std::ostream& out, const Command* c, int toDepth, bool types, size_t dag) const throw();
  void toStream(std::ostream& out, const CommandStatus* s) const throw();
  //for models
  void toStream(std::ostream& out, Model* m, const Command* c) const throw();
};/* class CvcPrinter */

}/* CVC4::printer::cvc namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__CVC_PRINTER_H */

