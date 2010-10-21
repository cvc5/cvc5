/*********************                                                        */
/*! \file options.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT.
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS_H
#define __CVC4__OPTIONS_H

#ifdef CVC4_DEBUG
#  define USE_EARLY_TYPE_CHECKING_BY_DEFAULT true
#else /* CVC4_DEBUG */
#  define USE_EARLY_TYPE_CHECKING_BY_DEFAULT false
#endif /* CVC4_DEBUG */

#include <iostream>
#include <string>

#include "util/language.h"

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
  InputLanguage inputLanguage;

  /** Enumeration of UF implementation choices */
  typedef enum { TIM, MORGAN } UfImplementation;

  /** Which implementation of uninterpreted function theory to use */
  UfImplementation uf_implementation;

  /** Should we exit after parsing? */
  bool parseOnly;

  /** Should the parser do semantic checks? */
  bool semanticChecks;

  /** Should the parser memory-map file input? */
  bool memoryMap;

  /** Should we strictly enforce the language standard while parsing? */
  bool strictParsing;

  /** Should we expand function definitions lazily? */
  bool lazyDefinitionExpansion;

  /** Whether we're in interactive mode or not */
  bool interactive;

  /**
   * Whether we're in interactive mode (or not) due to explicit user
   * setting (if false, we inferred the proper default setting).
   */
  bool interactiveSetByUser;

  /** Whether we support SmtEngine::getValue() for this run. */
  bool produceModels;

  /** Whether we support SmtEngine::getAssignment() for this run. */
  bool produceAssignments;

  /** Whether we do typechecking at all. */
  bool typeChecking;

  /** Whether we do typechecking at Expr creation time. */
  bool earlyTypeChecking;

  Options() :
    binary_name(),
    statistics(false),
    out(0),
    err(0),
    verbosity(0),
    inputLanguage(language::input::LANG_AUTO),
    uf_implementation(MORGAN),
    parseOnly(false),
    semanticChecks(true),
    memoryMap(false),
    strictParsing(false),
    lazyDefinitionExpansion(false),
    interactive(false),
    interactiveSetByUser(false),
    produceModels(false),
    produceAssignments(false),
    typeChecking(true),
    earlyTypeChecking(USE_EARLY_TYPE_CHECKING_BY_DEFAULT) {
  }
};/* struct Options */

inline std::ostream& operator<<(std::ostream& out,
                                Options::UfImplementation uf) {
  switch(uf) {
  case Options::TIM:
    out << "TIM";
    break;
  case Options::MORGAN:
    out << "MORGAN";
    break;
  default:
    out << "UfImplementation:UNKNOWN![" << unsigned(uf) << "]";
  }

  return out;
}

}/* CVC4 namespace */

#undef USE_EARLY_TYPE_CHECKING_BY_DEFAULT

#endif /* __CVC4__OPTIONS_H */
