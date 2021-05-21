/******************************************************************************
 * Top contributors (to current version):
 *   Christopher L. Conway, Morgan Deters, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "cvc/cvc.h"
#include "options/options.h"
#include "parser/antlr_input.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "smt2/smt2.h"
#include "tptp/tptp.h"

namespace cvc5 {
namespace parser {

ParserBuilder::ParserBuilder(api::Solver* solver, SymbolManager* sm)
    : d_solver(solver), d_symman(sm)
{
  init(solver, sm);
}

ParserBuilder::ParserBuilder(api::Solver* solver,
                             SymbolManager* sm,
                             const Options& options)
    : d_solver(solver), d_symman(sm)
{
  init(solver, sm);
  withOptions(options);
}

void ParserBuilder::init(api::Solver* solver, SymbolManager* sm)
{
  d_lang = language::input::LANG_AUTO;
  d_solver = solver;
  d_symman = sm;
  d_checksEnabled = true;
  d_strictMode = false;
  d_canIncludeFile = true;
  d_parseOnly = false;
  d_logicIsForced = false;
  d_forcedLogic = "";
}

Parser* ParserBuilder::build()
{
  Parser* parser = NULL;
  switch (d_lang)
  {
    case language::input::LANG_SYGUS_V2:
      parser = new Smt2(d_solver, d_symman, d_strictMode, d_parseOnly);
      break;
    case language::input::LANG_TPTP:
      parser = new Tptp(d_solver, d_symman, d_strictMode, d_parseOnly);
      break;
    default:
      if (language::isInputLang_smt2(d_lang))
      {
        parser = new Smt2(d_solver, d_symman, d_strictMode, d_parseOnly);
      }
      else
      {
        parser = new Cvc(d_solver, d_symman, d_strictMode, d_parseOnly);
      }
      break;
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

  if( d_logicIsForced ) {
    parser->forceLogic(d_forcedLogic);
  }

  return parser;
}

ParserBuilder& ParserBuilder::withChecks(bool flag) {
  d_checksEnabled = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withInputLanguage(InputLanguage lang) {
  d_lang = lang;
  return *this;
}

ParserBuilder& ParserBuilder::withParseOnly(bool flag) {
  d_parseOnly = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withOptions(const Options& options) {
  ParserBuilder& retval = *this;
  retval =
      retval.withInputLanguage(options.getInputLanguage())
      .withChecks(options.getSemanticChecks())
      .withStrictMode(options.getStrictParsing())
      .withParseOnly(options.getParseOnly())
      .withIncludeFile(options.getFilesystemAccess());
  if(options.wasSetByUserForceLogicString()) {
    LogicInfo tmp(options.getForceLogicString());
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

ParserBuilder& ParserBuilder::withForcedLogic(const std::string& logic) {
  d_logicIsForced = true;
  d_forcedLogic = logic;
  return *this;
}

}  // namespace parser
}  // namespace cvc5
