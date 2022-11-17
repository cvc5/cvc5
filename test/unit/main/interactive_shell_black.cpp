/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::InteractiveShell.
 */

#include <memory>
#include <sstream>
#include <vector>

#include "api/cpp/cvc5.h"
#include "main/interactive_shell.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/api/cpp/command.h"
#include "parser/api/cpp/symbol_manager.h"
#include "parser/parser_builder.h"
#include "test.h"

using namespace cvc5::parser;
using namespace cvc5::internal::parser;

namespace cvc5::internal {
namespace test {

class TestMainBlackInteractiveShell : public TestInternal
{
 protected:
  void SetUp() override
  {
    TestInternal::SetUp();

    d_sin = std::make_unique<std::stringstream>();
    d_sout = std::make_unique<std::stringstream>();

    d_solver.reset(new cvc5::Solver());
    d_solver->setOption("input-language", "smt2");
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
    uint32_t n = 0;
    while (n <= maxCommands)
    {
      std::optional<InteractiveShell::CmdSeq> cmds = shell.readCommand();
      if (!cmds)
      {
        break;
      }
      n += cmds->size();
    }
    ASSERT_LE(n, maxCommands);
    ASSERT_GE(n, minCommands);
  }

  std::unique_ptr<std::stringstream> d_sin;
  std::unique_ptr<std::stringstream> d_sout;
  std::unique_ptr<SymbolManager> d_symman;
  std::unique_ptr<cvc5::Solver> d_solver;
};

TEST_F(TestMainBlackInteractiveShell, assert_true)
{
  *d_sin << "(assert true)\n" << std::flush;
  InteractiveShell shell(d_solver.get(), d_symman.get(), *d_sin, *d_sout);
  countCommands(shell, 1, 1);
}

TEST_F(TestMainBlackInteractiveShell, query_false)
{
  *d_sin << "(check-sat)\n" << std::flush;
  InteractiveShell shell(d_solver.get(), d_symman.get(), *d_sin, *d_sout);
  countCommands(shell, 1, 1);
}

TEST_F(TestMainBlackInteractiveShell, def_use1)
{
  InteractiveShell shell(d_solver.get(), d_symman.get(), *d_sin, *d_sout);
  *d_sin << "(declare-const x Real) (assert (> x 0))\n" << std::flush;
  countCommands(shell, 2, 2);
}

TEST_F(TestMainBlackInteractiveShell, def_use2)
{
  InteractiveShell shell(d_solver.get(), d_symman.get(), *d_sin, *d_sout);
  /* readCommand may return a sequence, see above. */
  *d_sin << "(declare-const x Real)\n" << std::flush;
  shell.readCommand();
  *d_sin << "(assert (> x 0))\n" << std::flush;
  countCommands(shell, 1, 1);
}

TEST_F(TestMainBlackInteractiveShell, empty_line)
{
  InteractiveShell shell(d_solver.get(), d_symman.get(), *d_sin, *d_sout);
  *d_sin << std::flush;
  countCommands(shell, 0, 0);
}

TEST_F(TestMainBlackInteractiveShell, repeated_empty_lines)
{
  *d_sin << "\n\n\n";
  InteractiveShell shell(d_solver.get(), d_symman.get(), *d_sin, *d_sout);
  /* Might return up to four empties, might return nothing */
  countCommands(shell, 0, 3);
}
}  // namespace test
}  // namespace cvc5::internal
