/*********************                                                        */
/*! \file smt2_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

enum Variant {
  no_variant,
  smt2_0_variant, // old-style 2.0 syntax, when it makes a difference
  smt2_6_variant, // new-style 2.6 syntax, when it makes a difference
  z3str_variant, // old-style 2.0 and also z3str syntax
  sygus_variant  // variant for sygus
};/* enum Variant */

class Smt2Printer : public CVC4::Printer {
  Variant d_variant;

  void toStream(std::ostream& out, TNode n, int toDepth, bool types) const throw();
  void toStream(std::ostream& out, const Model& m, const Command* c) const throw();
public:
  Smt2Printer(Variant variant = no_variant) : d_variant(variant) { }
  using CVC4::Printer::toStream;
  void toStream(std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const throw();
  void toStream(std::ostream& out, const Command* c, int toDepth, bool types, size_t dag) const throw();
  void toStream(std::ostream& out, const CommandStatus* s) const throw();
  void toStream(std::ostream& out, const SExpr& sexpr) const throw();
  void toStream(std::ostream& out, const Model& m) const throw();
  void toStream(std::ostream& out, const UnsatCore& core, const std::map<Expr, std::string>& names) const throw();
};/* class Smt2Printer */

}/* CVC4::printer::smt2 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__SMT2_PRINTER_H */

