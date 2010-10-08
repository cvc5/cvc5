/*********************                                                        */
/*! \file language.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Definition of input and output languages
 **
 ** Definition of input and output languages.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LANGUAGE_H
#define __CVC4__LANGUAGE_H

#include <sstream>
#include <string>

#include "util/exception.h"

namespace CVC4 {
namespace language {

namespace input {

enum Language {
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  /** Auto-detect the language */
  LANG_AUTO = -1,

  // COMMON INPUT AND OUTPUT LANGUAGES HAVE ENUM VALUES IN [0,999]
  // AND SHOULD CORRESPOND IN PLACEMENT WITH OUTPUTLANGUAGE
  //
  // EVEN IF A LANGUAGE ISN'T CURRENTLY SUPPORTED AS AN INPUT OR
  // OUTPUT LANGUAGE, IF IT IS "IN PRINCIPLE" A COMMON LANGUAGE,
  // INCLUDE IT HERE

  /** The SMTLIB input language */
  LANG_SMTLIB = 0,
  /** The SMTLIB v2 input language */
  LANG_SMTLIB_V2,
  /** The CVC4 input language */
  LANG_CVC4

  // START INPUT-ONLY LANGUAGES AT ENUM VALUE 1000
  // THESE ARE IN PRINCIPLE NOT POSSIBLE OUTPUT LANGUAGES

};/* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) {
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
    out << "undefined_input_language";
  }
  return out;
}

}/* CVC4::language::input namespace */

namespace output {

enum Language {
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  // COMMON INPUT AND OUTPUT LANGUAGES HAVE ENUM VALUES IN [0,999]
  // AND SHOULD CORRESPOND IN PLACEMENT WITH INPUTLANGUAGE
  //
  // EVEN IF A LANGUAGE ISN'T CURRENTLY SUPPORTED AS AN INPUT OR
  // OUTPUT LANGUAGE, IF IT IS "IN PRINCIPLE" A COMMON LANGUAGE,
  // INCLUDE IT HERE

  /** The SMTLIB output language */
  LANG_SMTLIB = input::LANG_SMTLIB,
  /** The SMTLIB v2 output language */
  LANG_SMTLIB_V2 = input::LANG_SMTLIB_V2,
  /** The CVC4 output language */
  LANG_CVC4 = input::LANG_CVC4,

  // START OUTPUT-ONLY LANGUAGES AT ENUM VALUE 1000
  // THESE ARE IN PRINCIPLE NOT POSSIBLE INPUT LANGUAGES

  /** The AST output language */
  LANG_AST = 1000

};/* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) {
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
  case LANG_AST:
    out << "LANG_AUTO";
    break;
  default:
    out << "undefined_output_language";
  }
  return out;
}

}/* CVC4::language::output namespace */

}/* CVC4::language namespace */

typedef language::input::Language InputLanguage;
typedef language::output::Language OutputLanguage;

namespace language {

inline OutputLanguage toOutputLanguage(InputLanguage language) {
  switch(language) {
  case input::LANG_SMTLIB:
  case input::LANG_SMTLIB_V2:
  case input::LANG_CVC4:
    // these entries correspond
    return OutputLanguage(int(language));

  default: {
    std::stringstream ss;
    ss << "Cannot map input language `" << language
       << "' to an output language.";
    throw CVC4::Exception(ss.str());
  }
  }/* switch(language) */
}/* toOutputLanguage() */

}/* CVC4::language namespace */
}/* CVC4 namespace */

#endif /* __CVC4__LANGUAGE_H */
