/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Christopher L. Conway, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::parser::ParserBuilder.
 */

#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include <fstream>
#include <iostream>

#include "api/cpp/cvc5.h"
#include "expr/symbol_manager.h"
#include "options/language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "test_api.h"

namespace cvc5 {

using namespace parser;
using namespace language::input;

namespace test {

class TestParseBlackParserBuilder : public TestApi
{
 protected:
  void SetUp() override { d_symman.reset(new SymbolManager(&d_solver)); }

  void checkEmptyInput(ParserBuilder& builder)
  {
    Parser* parser = builder.build();
    ASSERT_NE(parser, nullptr);

    api::Term e = parser->nextExpression();
    ASSERT_TRUE(e.isNull());

    delete parser;
  }

  void checkTrueInput(ParserBuilder& builder)
  {
    Parser* parser = builder.build();
    ASSERT_NE(parser, nullptr);

    api::Term e = parser->nextExpression();
    ASSERT_EQ(e, d_solver.mkTrue());

    e = parser->nextExpression();
    ASSERT_TRUE(e.isNull());
    delete parser;
  }

  char* mkTemp()
  {
    char* filename = strdup("/tmp/testinput.XXXXXX");
    int32_t fd = mkstemp(filename);
    if (fd == -1) return nullptr;
    close(fd);
    return filename;
  }
  std::unique_ptr<SymbolManager> d_symman;
};

TEST_F(TestParseBlackParserBuilder, empty_file_input)
{
  char* filename = mkTemp();
  ASSERT_NE(filename, nullptr);

  checkEmptyInput(ParserBuilder(&d_solver, d_symman.get(), filename)
                      .withInputLanguage(LANG_CVC));

  remove(filename);
  free(filename);
}

TEST_F(TestParseBlackParserBuilder, simple_file_input)
{
  char* filename = mkTemp();

  std::fstream fs(filename, std::fstream::out);
  fs << "TRUE" << std::endl;
  fs.close();

  checkTrueInput(ParserBuilder(&d_solver, d_symman.get(), filename)
                     .withInputLanguage(LANG_CVC));

  remove(filename);
  free(filename);
}

TEST_F(TestParseBlackParserBuilder, empty_string_input)
{
  checkEmptyInput(ParserBuilder(&d_solver, d_symman.get(), "foo")
                      .withInputLanguage(LANG_CVC)
                      .withStringInput(""));
}

TEST_F(TestParseBlackParserBuilder, true_string_input)
{
  checkTrueInput(ParserBuilder(&d_solver, d_symman.get(), "foo")
                     .withInputLanguage(LANG_CVC)
                     .withStringInput("TRUE"));
}

TEST_F(TestParseBlackParserBuilder, empty_stream_input)
{
  std::stringstream ss("", std::ios_base::in);
  checkEmptyInput(ParserBuilder(&d_solver, d_symman.get(), "foo")
                      .withInputLanguage(LANG_CVC)
                      .withStreamInput(ss));
}

TEST_F(TestParseBlackParserBuilder, true_stream_input)
{
  std::stringstream ss("TRUE", std::ios_base::in);
  checkTrueInput(ParserBuilder(&d_solver, d_symman.get(), "foo")
                     .withInputLanguage(LANG_CVC)
                     .withStreamInput(ss));
}

}  // namespace test
}  // namespace cvc5
