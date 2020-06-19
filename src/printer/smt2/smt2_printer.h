/*********************                                                        */
/*! \file smt2_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the SMT2 output language
 **
 ** The pretty-printer interface for the SMT2 output language.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__SMT2_PRINTER_H
#define CVC4__PRINTER__SMT2_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace smt2 {

enum Variant
{
  no_variant,
  smt2_0_variant,  // old-style 2.0 syntax, when it makes a difference
  smt2_6_variant,  // new-style 2.6 syntax, when it makes a difference, with
                   // support for the string standard
  z3str_variant,   // old-style 2.0 and also z3str syntax
  sygus_variant    // variant for sygus
};                 /* enum Variant */
class Smt2Printer : public CVC4::Printer {
 public:
  Smt2Printer(Variant variant = no_variant) : d_variant(variant) { }
  using CVC4::Printer::toStream;
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
  /**
   * Writes the unsat core to the stream out.
   * We use the expression names that are stored in the SMT engine associated
   * with the core (UnsatCore::getSmtEngine) for printing named assertions.
   */
  void toStream(std::ostream& out, const UnsatCore& core) const override;
  /**
   * Write the term that sygus datatype term node n
   * encodes to a stream with this Printer.
   */
  void toStreamSygus(std::ostream& out, TNode n) const override;

 private:
  void toStream(
      std::ostream& out, TNode n, int toDepth, bool types, TypeNode nt) const;
  void toStream(std::ostream& out,
                const Model& m,
                const Command* c) const override;
  void toStream(std::ostream& out, const SExpr& sexpr) const;

  Variant d_variant;
};/* class Smt2Printer */

}/* CVC4::printer::smt2 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* CVC4__PRINTER__SMT2_PRINTER_H */
