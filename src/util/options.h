/*********************                                           -*- C++ -*-  */
/** options.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Global (command-line or equivalent) tuning parameters.
 **/

#include <iostream>

#ifndef __CVC4__OPTIONS_H
#define __CVC4__OPTIONS_H

namespace CVC4 {

struct Options {

  std::string binary_name;

  bool smtcomp_mode;
  bool statistics;

  std::ostream *out;
  std::ostream *err;

  /* -1 means no output */
  /* 0 is normal (and default) -- warnings only */
  /* 1 is warnings + notices so the user doesn't get too bored */
  /* 2 is chatty, giving statistical things etc. */
  /* with 3, the solver is slowed down by all the scrolling */
  int verbosity;

  /** The input language option */
  enum InputLanguage {
    /** The SMTLIB input language */
    LANG_SMTLIB,
    /** The CVC4 input language */
    LANG_CVC4,
    /** Auto-detect the language */
    LANG_AUTO
  };

  /** The input language */
  InputLanguage lang;

  Options() : binary_name(),
              smtcomp_mode(false),
              statistics(false),
              out(0),
              err(0),
              verbosity(0),
              lang(LANG_AUTO)
  {}
};/* struct Options */

}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS_H */
