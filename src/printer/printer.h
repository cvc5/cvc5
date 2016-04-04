/*********************                                                        */
/*! \file printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__PRINTER_H
#define __CVC4__PRINTER__PRINTER_H

#include <map>
#include <string>

#include "expr/node.h"
#include "options/language.h"
#include "smt/command.h"
#include "smt/model.h"
#include "util/sexpr.h"

namespace CVC4 {

class Printer {
  /** Printers for each OutputLanguage */
  static Printer* d_printers[language::output::LANG_MAX];

  /** Make a Printer for a given OutputLanguage */
  static Printer* makePrinter(OutputLanguage lang) throw();

  // disallow copy, assignment
  Printer(const Printer&) CVC4_UNDEFINED;
  Printer& operator=(const Printer&) CVC4_UNDEFINED;

protected:
  // derived classes can construct, but no one else.
  Printer() throw() {}
  virtual ~Printer() {}

  /** write model response to command */
  virtual void toStream(std::ostream& out, const Model& m, const Command* c) const throw() = 0;

  /** write model response to command using another language printer */
  void toStreamUsing(OutputLanguage lang, std::ostream& out, const Model& m, const Command* c) const throw() {
    getPrinter(lang)->toStream(out, m, c);
  }

public:
  /** Get the Printer for a given OutputLanguage */
  static Printer* getPrinter(OutputLanguage lang) throw();

  /** Write a Node out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, TNode n,
                        int toDepth, bool types, size_t dag) const throw() = 0;

  /** Write a Command out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Command* c,
                        int toDepth, bool types, size_t dag) const throw() = 0;

  /** Write a CommandStatus out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const CommandStatus* s) const throw() = 0;



  /** Write a Model out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Model& m) const throw();

  /** Write an UnsatCore out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const UnsatCore& core) const throw();

  /** Write an UnsatCore out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const UnsatCore& core, const std::map<Expr, std::string>& names) const throw();

};/* class Printer */

}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__PRINTER_H */
