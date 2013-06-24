/*********************                                                        */
/*! \file printer.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Clark Barrett, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__PRINTER_H
#define __CVC4__PRINTER__PRINTER_H

#include "util/language.h"
#include "util/sexpr.h"
#include "util/util_model.h"
#include "expr/node.h"
#include "expr/command.h"

namespace CVC4 {

class Printer {
  /** Printers for each OutputLanguage */
  static Printer* d_printers[language::output::LANG_MAX];

  /** Make a Printer for a given OutputLanguage */
  static Printer* makePrinter(OutputLanguage lang) throw();

  // disallow copy, assignment
  Printer(const Printer&) CVC4_UNUSED;
  Printer& operator=(const Printer&) CVC4_UNUSED;

protected:
  // derived classes can construct, but no one else.
  Printer() throw() {}

  /** write model response to command */
  virtual void toStream(std::ostream& out, const Model& m, const Command* c) const throw() = 0;

  /** write model response to command using another language printer */
  void toStreamUsing(OutputLanguage lang, std::ostream& out, const Model& m, const Command* c) const throw() {
    getPrinter(lang)->toStream(out, m, c);
  }

public:
  /** Get the Printer for a given OutputLanguage */
  static Printer* getPrinter(OutputLanguage lang) throw() {
    if(d_printers[lang] == NULL) {
      d_printers[lang] = makePrinter(lang);
    }
    return d_printers[lang];
  }

  /** Write a Node out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, TNode n,
                        int toDepth, bool types, size_t dag) const throw() = 0;

  /** Write a Command out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Command* c,
                        int toDepth, bool types, size_t dag) const throw() = 0;

  /** Write a CommandStatus out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const CommandStatus* s) const throw() = 0;

  /** Write an SExpr out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const SExpr& sexpr) const throw();

  /**
   * Write a Result out to a stream with this Printer.
   *
   * The default implementation writes a reasonable string in lowercase
   * for sat, unsat, valid, invalid, or unknown results.  This behavior
   * is overridable by each Printer, since sometimes an output language
   * has a particular preference for how results should appear.
   */
  virtual void toStream(std::ostream& out, const Result& r) const throw();

  /** Write a Model out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Model& m) const throw();

};/* class Printer */

}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__PRINTER_H */

