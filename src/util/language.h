/*********************                                                        */
/*! \file language.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "options/option_exception.h"

namespace CVC4 {
namespace language {

namespace input {

enum CVC4_PUBLIC Language {
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  /** Auto-detect the language */
  LANG_AUTO = -1,

  // COMMON INPUT AND OUTPUT LANGUAGES HAVE ENUM VALUES IN [0,9]
  // AND SHOULD CORRESPOND IN PLACEMENT WITH OUTPUTLANGUAGE
  //
  // EVEN IF A LANGUAGE ISN'T CURRENTLY SUPPORTED AS AN INPUT OR
  // OUTPUT LANGUAGE, IF IT IS "IN PRINCIPLE" A COMMON LANGUAGE,
  // INCLUDE IT HERE

  /** The SMTLIB v1 input language */
  LANG_SMTLIB_V1 = 0,
  /** The SMTLIB v2 input language */
  LANG_SMTLIB_V2,
  /** The TPTP input language */
  LANG_TPTP,
  /** The CVC4 input language */
  LANG_CVC4,
  /** The Z3-str input language */
  LANG_Z3STR,

  // START INPUT-ONLY LANGUAGES AT ENUM VALUE 10
  // THESE ARE IN PRINCIPLE NOT POSSIBLE OUTPUT LANGUAGES

  /** LANG_MAX is > any valid InputLanguage id */
  LANG_MAX
};/* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, Language lang) {
  switch(lang) {
  case LANG_AUTO:
    out << "LANG_AUTO";
    break;
  case LANG_SMTLIB_V1:
    out << "LANG_SMTLIB_V1";
    break;
  case LANG_SMTLIB_V2:
    out << "LANG_SMTLIB_V2";
    break;
  case LANG_TPTP:
    out << "LANG_TPTP";
    break;
  case LANG_CVC4:
    out << "LANG_CVC4";
    break;
  case LANG_Z3STR:
    out << "LANG_Z3STR";
    break;
  default:
    out << "undefined_input_language";
  }
  return out;
}

}/* CVC4::language::input namespace */

namespace output {

enum CVC4_PUBLIC Language {
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  /** Match the output language to the input language */
  LANG_AUTO = -1,

  // COMMON INPUT AND OUTPUT LANGUAGES HAVE ENUM VALUES IN [0,9]
  // AND SHOULD CORRESPOND IN PLACEMENT WITH INPUTLANGUAGE
  //
  // EVEN IF A LANGUAGE ISN'T CURRENTLY SUPPORTED AS AN INPUT OR
  // OUTPUT LANGUAGE, IF IT IS "IN PRINCIPLE" A COMMON LANGUAGE,
  // INCLUDE IT HERE

  /** The SMTLIB v1 output language */
  LANG_SMTLIB_V1 = input::LANG_SMTLIB_V1,
  /** The SMTLIB v2 output language */
  LANG_SMTLIB_V2 = input::LANG_SMTLIB_V2,
  /** The TPTP output language */
  LANG_TPTP = input::LANG_TPTP,
  /** The CVC4 output language */
  LANG_CVC4 = input::LANG_CVC4,
  /** The Z3-str output language */
  LANG_Z3STR = input::LANG_Z3STR,

  // START OUTPUT-ONLY LANGUAGES AT ENUM VALUE 10
  // THESE ARE IN PRINCIPLE NOT POSSIBLE INPUT LANGUAGES

  /** The AST output language */
  LANG_AST = 10,
  /** The CVC3-compatibility output language */
  LANG_CVC3,

  /** LANG_MAX is > any valid OutputLanguage id */
  LANG_MAX
};/* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, Language lang) {
  switch(lang) {
  case LANG_SMTLIB_V1:
    out << "LANG_SMTLIB_V1";
    break;
  case LANG_SMTLIB_V2:
    out << "LANG_SMTLIB_V2";
    break;
  case LANG_TPTP:
    out << "LANG_TPTP";
    break;
  case LANG_CVC4:
    out << "LANG_CVC4";
    break;
  case LANG_Z3STR:
    out << "LANG_Z3STR";
    break;
  case LANG_AST:
    out << "LANG_AST";
    break;
  case LANG_CVC3:
    out << "LANG_CVC3";
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

InputLanguage toInputLanguage(OutputLanguage language) CVC4_PUBLIC;
OutputLanguage toOutputLanguage(InputLanguage language) CVC4_PUBLIC;
InputLanguage toInputLanguage(std::string language) CVC4_PUBLIC;
OutputLanguage toOutputLanguage(std::string language) CVC4_PUBLIC;

}/* CVC4::language namespace */
}/* CVC4 namespace */

#endif /* __CVC4__LANGUAGE_H */
