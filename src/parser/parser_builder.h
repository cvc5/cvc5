/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Christopher L. Conway, Aina Niemetz
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

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_BUILDER_H
#define CVC5__PARSER__PARSER_BUILDER_H

#include <string>

#include "cvc5_export.h"
#include "options/language.h"
#include "parser/input.h"

namespace cvc5 {

class Solver;

class Options;

namespace parser {

class Parser;
class SymbolManager;

/**
 * A builder for input language parsers. <code>build()</code> can be
 * called any number of times on an instance and will generate a fresh
 * parser each time.
 */
class CVC5_EXPORT ParserBuilder
{
  /** The input language */
  std::string d_lang;

  /** The API Solver object. */
  cvc5::Solver* d_solver;

  /** The symbol manager */
  SymbolManager* d_symman;

  /** Should semantic checks be enabled during parsing? */
  bool d_checksEnabled;

  /** Should we parse in strict mode? */
  bool d_strictMode;

  /** Should we allow include-file commands? */
  bool d_canIncludeFile;

  /** Is the logic forced by the user? */
  bool d_logicIsForced;

  /** The forced logic name */
  std::string d_forcedLogic;

  /** Initialize this parser builder */
  void init(cvc5::Solver* solver, SymbolManager* sm);

 public:
  /** Create a parser builder using the given Solver and filename. */
  ParserBuilder(cvc5::Solver* solver, SymbolManager* sm, bool useOptions);

  /** Build the parser, using the current settings. */
  std::unique_ptr<Parser> build();

  /** Should semantic checks be enabled in the parser? (Default: yes) */
  ParserBuilder& withChecks(bool flag = true);

  /**
   * Set the input language to be used by the parser.
   *
   * (Default: LANG_AUTO)
   */
  ParserBuilder& withInputLanguage(const std::string& lang);

  /** Derive settings from the solver's options. */
  ParserBuilder& withOptions();

  /**
   * Should the parser use strict mode?
   *
   * (Default: no)
   */
  ParserBuilder& withStrictMode(bool flag = true);

  /**
   * Should the include-file commands be enabled?
   *
   * (Default: yes)
   */
  ParserBuilder& withIncludeFile(bool flag = true);

  /** Set the parser to use the given logic string. */
  ParserBuilder& withForcedLogic(const std::string& logic);
}; /* class ParserBuilder */

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__PARSER_BUILDER_H */
