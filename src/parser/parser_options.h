/*********************                                                        */
/*! \file parser_options.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PARSER__PARSER_OPTIONS_H
#define __CVC4__PARSER__PARSER_OPTIONS_H

#include <iostream>

namespace CVC4 {
namespace parser {

/** The input language option */
enum InputLanguage {
  /** The SMTLIB input language */
  LANG_SMTLIB,
  /** The SMTLIB v2 input language */
  LANG_SMTLIB_V2,
  /** The CVC4 input language */
  LANG_CVC4,
  /** Auto-detect the language */
  LANG_AUTO
};/* enum InputLanguage */

inline std::ostream& operator<<(std::ostream& out, InputLanguage lang) {
  switch(lang) {
  case LANG_SMTLIB:
    out << "LANG_SMTLIB";
    break;
  case LANG_SMTLIB_V2:
    out << "LANG_SMTLIB_V2";
    break;
  case LANG_CVC4:
    out << "LANG_CVC4";
    break;
  case LANG_AUTO:
    out << "LANG_AUTO";
    break;
  default:
    out << "undefined_language";
  }

  return out;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_OPTIONS_H */
