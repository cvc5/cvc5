/*********************                                                        */
/*! \file interactive_shell.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interactive shell for CVC4
 **/

#ifndef __CVC4__INTERACTIVE_SHELL_H
#define __CVC4__INTERACTIVE_SHELL_H

#include <iosfwd>
#include <string>

#include "options/language.h"
#include "options/options.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

class Command;
class ExprManager;
class Options;

namespace parser {
  class Parser;
}/* CVC4::parser namespace */

class CVC4_PUBLIC InteractiveShell {
  std::istream& d_in;
  std::ostream& d_out;
  parser::Parser* d_parser;
  const Options& d_options;
  bool d_quit;
  bool d_usingReadline;

  std::string d_historyFilename;

  static const std::string INPUT_FILENAME;
  static const unsigned s_historyLimit = 500;

public:
  InteractiveShell(ExprManager& exprManager, const Options& options);

  /**
   * Close out the interactive session.
   */
  ~InteractiveShell();

  /**
   * Read a command from the interactive shell. This will read as
   * many lines as necessary to parse a well-formed command.
   */
  Command* readCommand() throw (UnsafeInterruptException);

  /**
   * Return the internal parser being used.
   */
  parser::Parser* getParser() {
    return d_parser;
  }

};/* class InteractiveShell */

}/* CVC4 namespace */

#endif /* __CVC4__INTERACTIVE_SHELL_H */
