/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include "options/language.h"
#include "parser/api/cpp/command.h"
#include "parser/api/cpp/symbol_manager.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "test_api.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestParseBlackParserBuilder : public TestApi
{
 protected:
  void SetUp() override { d_symman.reset(new SymbolManager(&d_solver)); }

  void checkEmptyInput(Parser* parser)
  {
    cvc5::Term e = parser->nextExpression();
    ASSERT_TRUE(e.isNull());
  }

  void checkInput(Parser* parser, const std::string& expected)
  {
    Command* cmd = parser->nextCommand();
    ASSERT_NE(cmd, nullptr);
    ASSERT_EQ(cmd->toString(), expected);
    delete cmd;

    cmd = parser->nextCommand();
    ASSERT_EQ(cmd, nullptr);
    // e = parser->nextExpression();
    // ASSERT_TRUE(e.isNull());
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

  std::unique_ptr<Parser> parser(ParserBuilder(&d_solver, d_symman.get(), false)
                                     .withInputLanguage("LANG_SMTLIB_V2_6")
                                     .build());
  parser->setInput(Input::newFileInput("LANG_SMTLIB_V2_6", filename));
  checkEmptyInput(parser.get());

  remove(filename);
  free(filename);
}

TEST_F(TestParseBlackParserBuilder, simple_file_input)
{
  char* filename = mkTemp();

  std::fstream fs(filename, std::fstream::out);
  fs << "(set-logic ALL)" << std::endl;
  fs.close();

  std::unique_ptr<Parser> parser(ParserBuilder(&d_solver, d_symman.get(), false)
                                     .withInputLanguage("LANG_SMTLIB_V2_6")
                                     .build());
  parser->setInput(Input::newFileInput("LANG_SMTLIB_V2_6", filename));
  checkInput(parser.get(), "(set-logic ALL)\n");

  remove(filename);
  free(filename);
}

TEST_F(TestParseBlackParserBuilder, empty_string_input)
{
  std::unique_ptr<Parser> parser(ParserBuilder(&d_solver, d_symman.get(), false)
                                     .withInputLanguage("LANG_SMTLIB_V2_6")
                                     .build());
  parser->setInput(Input::newStringInput("LANG_SMTLIB_V2_6", "", "foo"));
  checkEmptyInput(parser.get());
}

TEST_F(TestParseBlackParserBuilder, true_string_input)
{
  std::unique_ptr<Parser> parser(ParserBuilder(&d_solver, d_symman.get(), false)
                                     .withInputLanguage("LANG_SMTLIB_V2_6")
                                     .build());
  parser->setInput(
      Input::newStringInput("LANG_SMTLIB_V2_6", "(assert true)", "foo"));
  checkInput(parser.get(), "(assert true)\n");
}

TEST_F(TestParseBlackParserBuilder, empty_stream_input)
{
  std::stringstream ss("", std::ios_base::in);
  std::unique_ptr<Parser> parser(ParserBuilder(&d_solver, d_symman.get(), false)
                                     .withInputLanguage("LANG_SMTLIB_V2_6")
                                     .build());
  parser->setInput(Input::newStreamInput("LANG_SMTLIB_V2_6", ss, "foo"));
  checkEmptyInput(parser.get());
}

TEST_F(TestParseBlackParserBuilder, true_stream_input)
{
  std::stringstream ss("(assert false)", std::ios_base::in);
  std::unique_ptr<Parser> parser(ParserBuilder(&d_solver, d_symman.get(), false)
                                     .withInputLanguage("LANG_SMTLIB_V2_6")
                                     .build());
  parser->setInput(Input::newStreamInput("LANG_SMTLIB_V2_6", ss, "foo"));
  checkInput(parser.get(), "(assert false)\n");
}

}  // namespace test
}  // namespace cvc5::internal
