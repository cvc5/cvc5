/*********************                                                        */
/*! \file printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__PRINTER_H
#define CVC4__PRINTER__PRINTER_H

#include <map>
#include <string>

#include "expr/node.h"
#include "options/language.h"
#include "smt/command.h"
#include "smt/model.h"
#include "util/sexpr.h"

namespace CVC4 {

class Printer
{
 public:
  /**
   * Since the printers are managed as unique_ptr, we need public acces to
   * the virtual destructor.
   */
  virtual ~Printer() {}

  /** Get the Printer for a given OutputLanguage */
  static Printer* getPrinter(OutputLanguage lang);

  /** Write a Node out to a stream with this Printer. */
  virtual void toStream(std::ostream& out,
                        TNode n,
                        int toDepth,
                        bool types,
                        size_t dag) const = 0;

  /** Write a Command out to a stream with this Printer. */
  virtual void toStream(std::ostream& out,
                        const Command* c,
                        int toDepth,
                        bool types,
                        size_t dag) const = 0;

  /** Write a CommandStatus out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const CommandStatus* s) const = 0;

  /** Write a Model out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const Model& m) const;

  /** Write an UnsatCore out to a stream with this Printer. */
  virtual void toStream(std::ostream& out, const UnsatCore& core) const;

  /** Print synth-fun command */
  virtual void toStreamCmdSynthFun(std::ostream& out,
                                   const std::string& sym,
                                   const std::vector<Node>& vars,
                                   TypeNode range,
                                   bool isInv,
                                   TypeNode sygusType);

 protected:
  /** Derived classes can construct, but no one else. */
  Printer() {}

  /** write model response to command */
  virtual void toStream(std::ostream& out,
                        const Model& m,
                        const Command* c) const = 0;

  /** write model response to command using another language printer */
  void toStreamUsing(OutputLanguage lang,
                     std::ostream& out,
                     const Model& m,
                     const Command* c) const
  {
    getPrinter(lang)->toStream(out, m, c);
  }

 private:
  /** Disallow copy, assignment  */
  Printer(const Printer&) = delete;
  Printer& operator=(const Printer&) = delete;

  /** Make a Printer for a given OutputLanguage */
  static std::unique_ptr<Printer> makePrinter(OutputLanguage lang);

  /** Printers for each OutputLanguage */
  static std::unique_ptr<Printer> d_printers[language::output::LANG_MAX];

}; /* class Printer */

}  // namespace CVC4

#endif /* CVC4__PRINTER__PRINTER_H */
