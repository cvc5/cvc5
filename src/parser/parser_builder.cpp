/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Christopher L. Conway, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A builder for parsers.
 */

// This must be included first.
#include "parser/parser_builder.h"

#include <string>

#include "api/cpp/cvc5.h"
#include "base/check.h"
#include "parser/antlr_input.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "smt2/smt2.h"
#include "tptp/tptp.h"

namespace cvc5 {
namespace parser {

ParserBuilder::ParserBuilder(cvc5::Solver* solver,
                             SymbolManager* sm,
                             bool useOptions)
    : d_solver(solver), d_symman(sm)
{
  init(solver, sm);
  if (useOptions)
  {
    withOptions();
  }
}

void ParserBuilder::init(cvc5::Solver* solver, SymbolManager* sm)
{
  d_lang = "LANG_AUTO";
  d_solver = solver;
  d_symman = sm;
  d_checksEnabled = true;
  d_strictMode = false;
  d_canIncludeFile = true;
  d_logicIsForced = false;
  d_forcedLogic = "";
}

std::unique_ptr<Parser> ParserBuilder::build()
{
  std::unique_ptr<Parser> parser;

  // Force the logic prior to building the parser. This makes a difference for
  // the TPTP parser, where forced logic is processed upon construction.
  if (d_logicIsForced)
  {
    d_symman->forceLogic(d_forcedLogic);
  }

  if (d_lang == "LANG_TPTP")
  {
    parser.reset(new Tptp(d_solver, d_symman, d_strictMode));
  }
  else
  {
    Assert(d_lang == "LANG_SYGUS_V2" || d_lang == "LANG_SMTLIB_V2_6");
    parser.reset(new Smt2(d_solver,
                          d_symman,
                          d_strictMode,
                          d_lang == "LANG_SYGUS_V2"));
  }

  if( d_checksEnabled ) {
    parser->enableChecks();
  } else {
    parser->disableChecks();
  }

  if( d_canIncludeFile ) {
    parser->allowIncludeFile();
  } else {
    parser->disallowIncludeFile();
  }


  return parser;
}

ParserBuilder& ParserBuilder::withChecks(bool flag) {
  d_checksEnabled = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withInputLanguage(const std::string& lang)
{
  d_lang = lang;
  return *this;
}

ParserBuilder& ParserBuilder::withOptions()
{
  ParserBuilder& retval = *this;
  retval = retval.withInputLanguage(d_solver->getOption("input-language"))
               .withChecks(d_solver->getOptionInfo("semantic-checks").boolValue())
               .withStrictMode(d_solver->getOptionInfo("strict-parsing").boolValue())
               .withIncludeFile(d_solver->getOptionInfo("filesystem-access").boolValue());
  auto info = d_solver->getOptionInfo("force-logic");
  if (info.setByUser)
  {
    internal::LogicInfo tmp(info.stringValue());
    retval = retval.withForcedLogic(tmp.getLogicString());
  }
  return retval;
}

ParserBuilder& ParserBuilder::withStrictMode(bool flag) {
  d_strictMode = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withIncludeFile(bool flag) {
  d_canIncludeFile = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withForcedLogic(const std::string& logic)
{
  d_logicIsForced = true;
  d_forcedLogic = logic;
  return *this;
}

}  // namespace parser
}  // namespace cvc5
