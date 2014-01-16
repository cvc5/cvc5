/*********************                                                        */
/*! \file printer.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds
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
#include "util/model.h"
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
    if(lang == language::output::LANG_AUTO) {
      // Infer the language to use for output.
      //
      // Options can be null in certain circumstances (e.g., when printing
      // the singleton "null" expr.  So we guard against segfault
      if(&Options::current() != NULL) {
        if(options::outputLanguage.wasSetByUser()) {
          lang = options::outputLanguage();
        }
        if(lang == language::output::LANG_AUTO && options::inputLanguage.wasSetByUser()) {
          lang = language::toOutputLanguage(options::inputLanguage());
        }
      }
      if(lang == language::output::LANG_AUTO) {
        lang = language::output::LANG_CVC4; // default
      }
    }
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

/**
 * IOStream manipulator to pretty-print SExprs.
 */
class PrettySExprs {
  /**
   * The allocated index in ios_base for our setting.
   */
  static const int s_iosIndex;

  /**
   * When this manipulator is used, the setting is stored here.
   */
  bool d_prettySExprs;

public:
  /**
   * Construct a PrettySExprs with the given setting.
   */
  PrettySExprs(bool prettySExprs) : d_prettySExprs(prettySExprs) {}

  inline void applyPrettySExprs(std::ostream& out) {
    out.iword(s_iosIndex) = d_prettySExprs;
  }

  static inline bool getPrettySExprs(std::ostream& out) {
    return out.iword(s_iosIndex);
  }

  static inline void setPrettySExprs(std::ostream& out, bool prettySExprs) {
    out.iword(s_iosIndex) = prettySExprs;
  }

  /**
   * Set the pretty-sexprs state on the output stream for the current
   * stack scope.  This makes sure the old state is reset on the
   * stream after normal OR exceptional exit from the scope, using the
   * RAII C++ idiom.
   */
  class Scope {
    std::ostream& d_out;
    bool d_oldPrettySExprs;

  public:

    inline Scope(std::ostream& out, bool prettySExprs) :
      d_out(out),
      d_oldPrettySExprs(PrettySExprs::getPrettySExprs(out)) {
      PrettySExprs::setPrettySExprs(out, prettySExprs);
    }

    inline ~Scope() {
      PrettySExprs::setPrettySExprs(d_out, d_oldPrettySExprs);
    }

  };/* class PrettySExprs::Scope */

};/* class PrettySExprs */

/**
 * Sets the default pretty-sexprs setting for an ostream.  Use like this:
 *
 *   // let out be an ostream, s an SExpr
 *   out << PrettySExprs(true) << s << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
inline std::ostream& operator<<(std::ostream& out, PrettySExprs ps) {
  ps.applyPrettySExprs(out);
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__PRINTER_H */

