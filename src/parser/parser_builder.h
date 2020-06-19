/*********************                                                        */
/*! \file parser_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A builder for parsers.
 **
 ** A builder for parsers.
 **/

#include "cvc4parser_public.h"

#ifndef CVC4__PARSER__PARSER_BUILDER_H
#define CVC4__PARSER__PARSER_BUILDER_H

#include <string>

#include "options/language.h"
#include "parser/input.h"

namespace CVC4 {

class Options;

namespace api {
class Solver;
}

namespace parser {

class Parser;

/**
 * A builder for input language parsers. <code>build()</code> can be
 * called any number of times on an instance and will generate a fresh
 * parser each time.
 */
class CVC4_PUBLIC ParserBuilder {
  enum InputType {
    FILE_INPUT,
    LINE_BUFFERED_STREAM_INPUT,
    STREAM_INPUT,
    STRING_INPUT
  };

  /** The input type. */
  InputType d_inputType;

  /** The input language */
  InputLanguage d_lang;

  /** The file name (may not exist) */
  std::string d_filename;

  /** The string input, if any. */
  std::string d_stringInput;

  /** The stream input, if any. */
  std::istream* d_streamInput;

  /** The API Solver object. */
  api::Solver* d_solver;

  /** Should semantic checks be enabled during parsing? */
  bool d_checksEnabled;

  /** Should we parse in strict mode? */
  bool d_strictMode;

  /** Should we allow include-file commands? */
  bool d_canIncludeFile;

  /** Should we memory-map a file input? */
  bool d_mmap;

  /** Are we parsing only? */
  bool d_parseOnly;

  /** Is the logic forced by the user? */
  bool d_logicIsForced;

  /** The forced logic name */
  std::string d_forcedLogic;

  /** Initialize this parser builder */
  void init(api::Solver* solver, const std::string& filename);

 public:
  /** Create a parser builder using the given Solver and filename. */
  ParserBuilder(api::Solver* solver, const std::string& filename);

  ParserBuilder(api::Solver* solver,
                const std::string& filename,
                const Options& options);

  /** Build the parser, using the current settings. */
  Parser* build();

  /** Should semantic checks be enabled in the parser? (Default: yes) */
  ParserBuilder& withChecks(bool flag = true);

  /** Set the Solver to use with the parser. */
  ParserBuilder& withSolver(api::Solver* solver);

  /** Set the parser to read a file for its input. (Default) */
  ParserBuilder& withFileInput();

  /**
   * Set the filename for use by the parser. If file input is used,
   * this file will be opened and read by the parser. Otherwise, the
   * filename string (possibly a non-existent path) will only be used
   * in error messages.
   */
  ParserBuilder& withFilename(const std::string& filename);

  /**
   * Set the input language to be used by the parser.
   *
   * (Default: LANG_AUTO)
   */
  ParserBuilder& withInputLanguage(InputLanguage lang);

  /**
   * Should the parser memory-map its input? This is only relevant if
   * the parser will have a file input.
   *
   * (Default: no)
   */
  ParserBuilder& withMmap(bool flag = true);

  /**
   * Are we only parsing, or doing something with the resulting
   * commands and expressions?  This setting affects whether the
   * parser will raise certain errors about unimplemented features,
   * even if there isn't a parsing error, because the result of the
   * parse would otherwise be an incorrect parse tree and the error
   * would go undetected.  This is specifically for circumstances
   * where the parser is ahead of the functionality present elsewhere
   * in CVC4 (such as quantifiers, subtypes, records, etc. in the CVC
   * language parser).
   */
  ParserBuilder& withParseOnly(bool flag = true);

  /** Derive settings from the given options. */
  ParserBuilder& withOptions(const Options& options);

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

  /** Set the parser to use the given stream for its input. */
  ParserBuilder& withStreamInput(std::istream& input);

  /** Set the parser to use the given stream for its input. */
  ParserBuilder& withLineBufferedStreamInput(std::istream& input);

  /** Set the parser to use the given string for its input. */
  ParserBuilder& withStringInput(const std::string& input);

  /** Set the parser to use the given logic string. */
  ParserBuilder& withForcedLogic(const std::string& logic);
};/* class ParserBuilder */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* CVC4__PARSER__PARSER_BUILDER_H */
