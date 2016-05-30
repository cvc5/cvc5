/*********************                                                        */
/*! \file ast_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
  void toStream(std::ostream& out, TNode n, int toDepth, bool types) const throw();
  void toStream(std::ostream& out, const Model& m, const Command* c) const throw();
public:
  using CVC4::Printer::toStream;
  void toStream(std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const throw();
  void toStream(std::ostream& out, const Command* c, int toDepth, bool types, size_t dag) const throw();
  void toStream(std::ostream& out, const CommandStatus* s) const throw();
  void toStream(std::ostream& out, const Model& m) const throw();
};/* class AstPrinter */

}/* CVC4::printer::ast namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__AST_PRINTER_H */

