/*********************                                                        */
/*! \file printer.h
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
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__PRINTER_H
#define __CVC4__PRINTER__PRINTER_H

#include "util/language.h"
#include "expr/node.h"
#include "expr/command.h"

namespace CVC4 {

class Printer {
  /** Printers for each OutputLanguage */
  static Printer* d_printers[language::output::LANG_MAX];

  /** Make a Printer for a given OutputLanguage */
  static Printer* makePrinter(OutputLanguage lang);

public:
  /** Get the Printer for a given OutputLanguage */
  static Printer* getPrinter(OutputLanguage lang) {
    if(d_printers[lang] == NULL) {
      d_printers[lang] = makePrinter(lang);
    }
    return d_printers[lang];
  }

  /** Write a Node out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, TNode n,
                        int toDepth, bool types) const = 0;

  /** Write a Command out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Command* c,
                        int toDepth, bool types) const = 0;
};/* class Printer */

}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__PRINTER_H */

