/*********************                                                        */
/*! \file interactive_shell.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interactive shell for CVC4
 **/

#ifndef CVC4__INTERACTIVE_SHELL_H
#define CVC4__INTERACTIVE_SHELL_H

#include <iosfwd>
#include <string>

#include "options/language.h"
#include "options/options.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

class Command;
class Options;

namespace api {
class Solver;
}

namespace parser {
  class Parser;
}/* CVC4::parser namespace */

class CVC4_PUBLIC InteractiveShell
{
  const Options& d_options;
  std::istream& d_in;
  std::ostream& d_out;
  parser::Parser* d_parser;
  bool d_quit;
  bool d_usingEditline;

  std::string d_historyFilename;

  static const std::string INPUT_FILENAME;
  static const unsigned s_historyLimit = 500;

public:
 InteractiveShell(api::Solver* solver);

 /**
  * Close out the interactive session.
  */
 ~InteractiveShell();

 /**
  * Read a command from the interactive shell. This will read as
  * many lines as necessary to parse a well-formed command.
  */
 Command* readCommand();

 /**
  * Return the internal parser being used.
  */
 parser::Parser* getParser() { return d_parser; }

};/* class InteractiveShell */

}/* CVC4 namespace */

#endif /* CVC4__INTERACTIVE_SHELL_H */
