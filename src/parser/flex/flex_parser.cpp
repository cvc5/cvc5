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

FlexParser::FlexParser(Solver* solver, SymbolManager* sm)
    : d_solver(solver), d_sm(sm)
{
}

void FlexParser::setFileInput(const std::string& filename)
{
  d_flexInput = FlexInput::mkFileInput(filename);
  initializeInput(d_flexInput->getStream(), filename);
}

void FlexParser::setStreamInput(std::istream& input, const std::string& name)
{
  d_flexInput = FlexInput::mkStreamInput(input);
  initializeInput(d_flexInput->getStream(), name);
}

void FlexParser::setStringInput(const std::string& input,
                                const std::string& name)
{
  d_flexInput = FlexInput::mkStringInput(input);
  initializeInput(d_flexInput->getStream(), name);
}

std::unique_ptr<FlexParser> FlexParser::mkFlexParser(const std::string& lang,
                                                     Solver* solver,
                                                     SymbolManager* sm)
{
  std::unique_ptr<FlexParser> parser;
  if (lang == "LANG_SYGUS_V2" || lang == "LANG_SMTLIB_V2_6")
  {
    bool isSygus = (lang == "LANG_SYGUS_V2");
    parser.reset(new Smt2Parser(solver, sm, isSygus));
  }
  else if (lang == "LANG_TPTP")
  {
    // TODO
  }
  return parser;
}

}  // namespace parser
}  // namespace cvc5
