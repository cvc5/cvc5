/*********************                                                        */
/*! \file interactive_shell_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Christopher L. Conway, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::InteractiveShell.
 **
 ** Black box testing of CVC4::InteractiveShell.
 **/

#include <sstream>
#include <vector>

#include "api/cvc4cpp.h"
#include "expr/expr_manager.h"
#include "expr/symbol_manager.h"
#include "main/interactive_shell.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/parser_builder.h"
#include "smt/command.h"
#include "test.h"

namespace CVC4 {
namespace test {

class TestMainBlackInteractiveShell : public TestInternal
{
 protected:
  void SetUp() override
  {
    TestInternal::SetUp();
    d_sin.reset(new std::stringstream);
    d_sout.reset(new std::stringstream);
    d_options.set(options::in, d_sin.get());
    d_options.set(options::out, d_sout.get());
    d_options.set(options::inputLanguage, language::input::LANG_CVC4);
    d_solver.reset(new CVC4::api::Solver(&d_options));
    d_symman.reset(new SymbolManager(d_solver.get()));
  }

  void TearDown() override
  {
    d_sin.reset(nullptr);
    d_sout.reset(nullptr);
    // ensure that symbol manager is destroyed before solver
    d_symman.reset(nullptr);
    d_solver.reset(nullptr);
  }

  /**
   * Read up to maxCommands+1 from the shell and throw an assertion error if
   * it's fewer than minCommands and more than maxCommands.  Note that an
   * empty string followed by EOF may be returned as an empty command, and
   * not NULL (subsequent calls to readCommand() should return NULL). E.g.,
   * "CHECKSAT;\n" may return two commands: the CHECKSAT, followed by an
   * empty command, followed by NULL.
   */
  void countCommands(InteractiveShell& shell,
                     uint32_t minCommands,
                     uint32_t maxCommands)
  {
    Command* cmd;
    uint32_t n = 0;
    while (n <= maxCommands && (cmd = shell.readCommand()) != NULL)
    {
      ++n;
      delete cmd;
    }
    ASSERT_LE(n, maxCommands);
    ASSERT_GE(n, minCommands);
  }

  std::unique_ptr<std::stringstream> d_sin;
  std::unique_ptr<std::stringstream> d_sout;
  std::unique_ptr<SymbolManager> d_symman;
  std::unique_ptr<CVC4::api::Solver> d_solver;
  Options d_options;
};

TEST_F(TestMainBlackInteractiveShell, assert_true)
{
  *d_sin << "ASSERT TRUE;\n" << std::flush;
  InteractiveShell shell(d_solver.get(), d_symman.get());
  countCommands(shell, 1, 1);
}

TEST_F(TestMainBlackInteractiveShell, query_false)
{
  *d_sin << "QUERY FALSE;\n" << std::flush;
  InteractiveShell shell(d_solver.get(), d_symman.get());
  countCommands(shell, 1, 1);
}

TEST_F(TestMainBlackInteractiveShell, def_use1)
{
  InteractiveShell shell(d_solver.get(), d_symman.get());
  *d_sin << "x : REAL; ASSERT x > 0;\n" << std::flush;
  /* readCommand may return a sequence, so we can't say for sure
     whether it will return 1 or 2... */
  countCommands(shell, 1, 2);
}

TEST_F(TestMainBlackInteractiveShell, def_use2)
{
  InteractiveShell shell(d_solver.get(), d_symman.get());
  /* readCommand may return a sequence, see above. */
  *d_sin << "x : REAL;\n" << std::flush;
  Command* tmp = shell.readCommand();
  *d_sin << "ASSERT x > 0;\n" << std::flush;
  countCommands(shell, 1, 1);
  delete tmp;
}

TEST_F(TestMainBlackInteractiveShell, empty_line)
{
  InteractiveShell shell(d_solver.get(), d_symman.get());
  *d_sin << std::flush;
  countCommands(shell, 0, 0);
}

TEST_F(TestMainBlackInteractiveShell, repeated_empty_lines)
{
  *d_sin << "\n\n\n";
  InteractiveShell shell(d_solver.get(), d_symman.get());
  /* Might return up to four empties, might return nothing */
  countCommands(shell, 0, 3);
}
}  // namespace test
}  // namespace CVC4
