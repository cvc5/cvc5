/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for tests that have access to an SMT-LIB parser
 * (for easily issuing commands and parsing terms).
 */

#ifndef CVC5__TEST__UNIT__TEST_API_H
#define CVC5__TEST__UNIT__TEST_API_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include "gtest/gtest.h"

#include "expr/node.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

/**
 * For writing tests that accesss an SMT-LIB parser.
 *
 * The parser is set to logic ALL.
 */
class TestWithSmtParser : public TestInternal
{
 protected:

  void SetUp() override
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_solver->setLogic("ALL");
    d_symman.reset(new parser::SymbolManager(d_solver.get()));
    d_ip.reset(new parser::InputParser(d_solver.get(), d_symman.get()));
  }

  void TearDown() override
  {
    d_symman.reset(nullptr);
    d_ip.reset(nullptr);
  }

  cvc5::TermManager d_tm;
  std::unique_ptr<cvc5::Solver> d_solver;
  std::unique_ptr<parser::SymbolManager> d_symman;
  std::unique_ptr<cvc5::parser::InputParser> d_ip;

 public:

  /**
   * Run this SMT-LIB command.
   */
  void doCommand(const std::string& s)
  {
    d_ip->setStringInput(modes::InputLanguage::SMT_LIB_2_6, s, "temp");
    auto command = d_ip->nextCommand();
    command.invoke(d_solver.get(), d_symman.get(), std::cout);
  }

  /**
   * Parse a node from SMT-LIB.
   */
  Node parseNode(const std::string& s)
  {
    d_ip->setStringInput(modes::InputLanguage::SMT_LIB_2_6, s, "temp");
    return *d_ip->nextTerm().d_node;
  }

};

}  // namespace test
}  // namespace cvc5::internal
#endif

