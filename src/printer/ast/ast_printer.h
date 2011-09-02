/*********************                                                        */
/*! \file ast_printer.h
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
 ** \brief The pretty-printer interface for the AST output language
 **
 ** The pretty-printer interface for the AST output language.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__AST_PRINTER_H
#define __CVC4__PRINTER__AST_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace ast {

class AstPrinter : public CVC4::Printer {
public:
  void toStream(std::ostream& out, TNode n, int toDepth, bool types) const;
  void toStream(std::ostream& out, const Command* c, int toDepth, bool types) const;
};/* class AstPrinter */

}/* CVC4::printer::ast namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__AST_PRINTER_H */

