/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 tokens.
 */

#include "parser/flex/flex_parser.h"

#include "parser/flex/smt2_parser.h"

namespace cvc5 {
namespace parser {

FlexParser::FlexParser()
{
  
}

void FlexParser::setFileInput(const std::string& filename)
{
  d_flexInput = FileInput::mkFileInput(filename);
  initializeInput(d_flexInput->getStream(), filename);
}

void FlexParser::setStreamInput(std::istream& input, const std::string& name)
{
  d_flexInput = FileInput::mkStreamInput(input);
  initializeInput(d_flexInput->getStream(), name);
}

void FlexParser::setStringInput(const std::string& input, const std::string& name)
{
  d_flexInput = FileInput::mkStringInput(input);
  initializeInput(d_flexInput->getStream(), name);
}

std::unique_ptr<FlexParser> FlexParser::mkFlexParser(const std::string& lang)
{
  std::unique_ptr<Parser> parser;
  if (lang == "LANG_SYGUS_V2" || lang == "LANG_SMTLIB_V2_6"s)
  {
    parser.reset(new Tptp(d_solver, d_symman, d_strictMode, d_parseOnly));
  }
  else if (lang == "LANG_TPTP" )
  {
    Assert(d_lang == "LANG_SYGUS_V2" || d_lang == "LANG_SMTLIB_V2_6");
    parser.reset(new Smt2(d_solver, d_symman, d_strictMode, d_parseOnly));
  }
  return parser;
}

}  // namespace parser
}  // namespace cvc5
