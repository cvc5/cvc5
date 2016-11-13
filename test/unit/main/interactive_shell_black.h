/*********************                                                        */
/*! \file interactive_shell_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::InteractiveShell.
 **
 ** Black box testing of CVC4::InteractiveShell.
 **/

#include <cxxtest/TestSuite.h>

//Used in some of the tests
#include <vector>
#include <sstream>

#include "expr/expr_manager.h"
#include "main/interactive_shell.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/parser_builder.h"
#include "smt/command.h"

using namespace CVC4;
using namespace std;

class InteractiveShellBlack : public CxxTest::TestSuite {
private:
  ExprManager* d_exprManager;
  Options d_options;
  stringstream* d_sin;
  stringstream* d_sout;

  /** Read up to maxCommands+1 from the shell and throw an assertion
      error if it's fewer than minCommands and more than maxCommands.
      Note that an empty string followed by EOF may be returned as an
      empty command, and not NULL (subsequent calls to readCommand()
      should return NULL). E.g., "CHECKSAT;\n" may return two
      commands: the CHECKSAT, followed by an empty command, followed
      by NULL. */
  void countCommands(InteractiveShell& shell, 
                     int minCommands, 
                     int maxCommands) {
    Command* cmd;
    int n = 0;
    while( n <= maxCommands && (cmd = shell.readCommand()) != NULL ) {
      ++n;
      delete cmd;
    }
    TS_ASSERT( n <= maxCommands );
    TS_ASSERT( n >= minCommands );
  }

 public:
  void setUp() {
    d_exprManager = new ExprManager;
    d_sin = new stringstream;
    d_sout = new stringstream;
    d_options.set(options::in, d_sin);
    d_options.set(options::out, d_sout);
    d_options.set(options::inputLanguage, language::input::LANG_CVC4);
  }

  void tearDown() {
    delete d_exprManager;
    delete d_sin;
    delete d_sout;
  }

  void testAssertTrue() {
    *d_sin << "ASSERT TRUE;\n" << flush;
    InteractiveShell shell(*d_exprManager, d_options);
    countCommands( shell, 1, 1 );
  }

  void testQueryFalse() {
    *d_sin << "QUERY FALSE;\n" << flush;
    InteractiveShell shell(*d_exprManager, d_options);
    countCommands( shell, 1, 1 );
  }

  void testDefUse() {
    InteractiveShell shell(*d_exprManager, d_options);
    *d_sin << "x : REAL; ASSERT x > 0;\n" << flush;
    /* readCommand may return a sequence, so we can't say for sure
       whether it will return 1 or 2... */
    countCommands( shell, 1, 2 );
  }

  void testDefUse2() {
    InteractiveShell shell(*d_exprManager, d_options);
    /* readCommand may return a sequence, see above. */
    *d_sin << "x : REAL;\n" << flush;
    Command* tmp = shell.readCommand();
    *d_sin << "ASSERT x > 0;\n" << flush;
    countCommands( shell, 1, 1 );
    delete tmp;
  }

  void testEmptyLine() {
    InteractiveShell shell(*d_exprManager, d_options);
    *d_sin << flush;
    countCommands(shell,0,0);
  }

  void testRepeatedEmptyLines() {
    *d_sin << "\n\n\n";
    InteractiveShell shell(*d_exprManager, d_options);
    /* Might return up to four empties, might return nothing */
    countCommands( shell, 0, 3 );
  }

};
