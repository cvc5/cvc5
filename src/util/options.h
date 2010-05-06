/*********************                                                        */
/** options.h
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Global (command-line or equivalent) tuning parameters.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS_H
#define __CVC4__OPTIONS_H

#include <iostream>
#include <string>

#include "parser/parser_options.h"

namespace CVC4 {

struct CVC4_PUBLIC Options {

  std::string binary_name;

  bool statistics;

  std::ostream *out;
  std::ostream *err;

  /* -1 means no output */
  /* 0 is normal (and default) -- warnings only */
  /* 1 is warnings + notices so the user doesn't get too bored */
  /* 2 is chatty, giving statistical things etc. */
  /* with 3, the solver is slowed down by all the scrolling */
  int verbosity;

  /** The input language */
  parser::InputLanguage lang;

  /** Should we exit after parsing? */
  bool parseOnly;

  /** Should the parser do semantic checks? */
  bool semanticChecks;

  /** Should the parser memory-map file input? */
  bool memoryMap;

  /** Should we strictly enforce the language standard while parsing? */
  bool strictParsing;

  Options() : binary_name(),
              statistics(false),
              out(0),
              err(0),
              verbosity(0),
              lang(parser::LANG_AUTO),
              parseOnly(false),
              semanticChecks(true),
              memoryMap(false),
              strictParsing(false)
  {}
};/* struct Options */

}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS_H */
