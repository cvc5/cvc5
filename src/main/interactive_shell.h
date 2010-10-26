/*********************                                                        */
/*! \file interactive_shell.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interactive shell for CVC4
 **/

#ifndef __CVC4__INTERACTIVE_SHELL_H
#define __CVC4__INTERACTIVE_SHELL_H

#include <iostream>
#include <string>

#include "util/language.h"

namespace CVC4 {

  class Command;
  class ExprManager;
  class Options;

  namespace parser {
    class Parser;
  }

class CVC4_PUBLIC InteractiveShell {
  std::istream& d_in;
  std::ostream& d_out;
  parser::Parser* d_parser;
  const InputLanguage d_language;

  static const std::string INPUT_FILENAME;

public:
  InteractiveShell(ExprManager& exprManager,
                   const Options& options);

  /** Read a command from the interactive shell. This will read as
      many lines as necessary to parse a well-formed command. */
  Command *readCommand();
};

} // CVC4 namespace

#endif // __CVC4__INTERACTIVE_SHELL_H
