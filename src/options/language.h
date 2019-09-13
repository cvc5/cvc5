/*********************                                                        */
/*! \file language.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definition of input and output languages
 **
 ** Definition of input and output languages.
 **/

#include "cvc4_public.h"

#ifndef CVC4__LANGUAGE_H
#define CVC4__LANGUAGE_H

#include <sstream>
#include <string>

#include "base/exception.h"
#include "options/option_exception.h"

namespace CVC4 {
namespace language {

namespace input {

enum CVC4_PUBLIC Language
{
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  /** Auto-detect the language */
  LANG_AUTO = -1,

  // COMMON INPUT AND OUTPUT LANGUAGES HAVE ENUM VALUES IN [0,9]
  // AND SHOULD CORRESPOND IN PLACEMENT WITH OUTPUTLANGUAGE
  //
  // EVEN IF A LANGUAGE ISN'T CURRENTLY SUPPORTED AS AN INPUT OR
  // OUTPUT LANGUAGE, IF IT IS "IN PRINCIPLE" A COMMON LANGUAGE,
  // INCLUDE IT HERE

  /** The SMTLIB v2.0 input language */
  LANG_SMTLIB_V2_0 = 0,
  /** The SMTLIB v2.5 input language */
  LANG_SMTLIB_V2_5,
  /** The SMTLIB v2.6 input language */
  LANG_SMTLIB_V2_6,
  /** Backward-compatibility for enumeration naming */
  LANG_SMTLIB_V2 = LANG_SMTLIB_V2_6,
  /** The SMTLIB v2.6 input language, with support for the strings standard */
  LANG_SMTLIB_V2_6_1,
  /** The TPTP input language */
  LANG_TPTP,
  /** The CVC4 input language */
  LANG_CVC4,
  /** The Z3-str input language */
  LANG_Z3STR,
  /** The SyGuS input language */
  LANG_SYGUS,
  /** The SyGuS input language version 2.0 */
  LANG_SYGUS_V2,

  // START OUTPUT-ONLY LANGUAGES AT ENUM VALUE 10
  // THESE ARE IN PRINCIPLE NOT POSSIBLE INPUT LANGUAGES

  /** LANG_MAX is > any valid InputLanguage id */
  LANG_MAX
}; /* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, Language lang) {
  switch(lang) {
  case LANG_AUTO:
    out << "LANG_AUTO";
    break;
  case LANG_SMTLIB_V2_0:
    out << "LANG_SMTLIB_V2_0";
    break;
  case LANG_SMTLIB_V2_5:
    out << "LANG_SMTLIB_V2_5";
    break;
  case LANG_SMTLIB_V2_6:
    out << "LANG_SMTLIB_V2_6";
    break;
  case LANG_SMTLIB_V2_6_1: out << "LANG_SMTLIB_V2_6_1"; break;
  case LANG_TPTP:
    out << "LANG_TPTP";
    break;
  case LANG_CVC4:
    out << "LANG_CVC4";
    break;
  case LANG_Z3STR:
    out << "LANG_Z3STR";
    break;
  case LANG_SYGUS:
    out << "LANG_SYGUS";
    break;
  case LANG_SYGUS_V2: out << "LANG_SYGUS_V2"; break;
  default:
    out << "undefined_input_language";
  }
  return out;
}

}/* CVC4::language::input namespace */

namespace output {

enum CVC4_PUBLIC Language
{
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  /** Match the output language to the input language */
  LANG_AUTO = -1,

  // COMMON INPUT AND OUTPUT LANGUAGES HAVE ENUM VALUES IN [0,9]
  // AND SHOULD CORRESPOND IN PLACEMENT WITH INPUTLANGUAGE
  //
  // EVEN IF A LANGUAGE ISN'T CURRENTLY SUPPORTED AS AN INPUT OR
  // OUTPUT LANGUAGE, IF IT IS "IN PRINCIPLE" A COMMON LANGUAGE,
  // INCLUDE IT HERE

  /** The SMTLIB v2.0 output language */
  LANG_SMTLIB_V2_0 = input::LANG_SMTLIB_V2_0,
  /** The SMTLIB v2.5 output language */
  LANG_SMTLIB_V2_5 = input::LANG_SMTLIB_V2_5,
  /** The SMTLIB v2.6 output language */
  LANG_SMTLIB_V2_6 = input::LANG_SMTLIB_V2_6,
  /** Backward-compatibility for enumeration naming */
  LANG_SMTLIB_V2 = input::LANG_SMTLIB_V2,
  /** The SMTLIB v2.6 output language */
  LANG_SMTLIB_V2_6_1 = input::LANG_SMTLIB_V2_6_1,
  /** The TPTP output language */
  LANG_TPTP = input::LANG_TPTP,
  /** The CVC4 output language */
  LANG_CVC4 = input::LANG_CVC4,
  /** The Z3-str output language */
  LANG_Z3STR = input::LANG_Z3STR,
  /** The sygus output language */
  LANG_SYGUS = input::LANG_SYGUS,
  /** The sygus output language version 2.0 */
  LANG_SYGUS_V2 = input::LANG_SYGUS_V2,

  // START OUTPUT-ONLY LANGUAGES AT ENUM VALUE 10
  // THESE ARE IN PRINCIPLE NOT POSSIBLE INPUT LANGUAGES

  /** The AST output language */
  LANG_AST = 10,
  /** The CVC3-compatibility output language */
  LANG_CVC3,

  /** LANG_MAX is > any valid OutputLanguage id */
  LANG_MAX
}; /* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, Language lang) {
  switch(lang) {
  case LANG_SMTLIB_V2_0:
    out << "LANG_SMTLIB_V2_0";
    break;
  case LANG_SMTLIB_V2_5:
    out << "LANG_SMTLIB_V2_5";
    break;
  case LANG_SMTLIB_V2_6: out << "LANG_SMTLIB_V2_6"; break;
  case LANG_SMTLIB_V2_6_1: out << "LANG_SMTLIB_V2_6_1"; break;
  case LANG_TPTP:
    out << "LANG_TPTP";
    break;
  case LANG_CVC4:
    out << "LANG_CVC4";
    break;
  case LANG_Z3STR:
    out << "LANG_Z3STR";
    break;
  case LANG_SYGUS:
    out << "LANG_SYGUS";
    break;
  case LANG_SYGUS_V2: out << "LANG_SYGUS_V2"; break;
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

/** Is the language a variant of the smtlib version 2 language? */
bool isInputLang_smt2(InputLanguage lang) CVC4_PUBLIC;
bool isOutputLang_smt2(OutputLanguage lang) CVC4_PUBLIC;

/**
  * Is the language smtlib 2.5 or above? If exact=true, then this method returns
  * false if the input language is not exactly SMT-LIB 2.6.
  */
bool isInputLang_smt2_5(InputLanguage lang, bool exact = false) CVC4_PUBLIC;
bool isOutputLang_smt2_5(OutputLanguage lang, bool exact = false) CVC4_PUBLIC;
/**
  * Is the language smtlib 2.6 or above? If exact=true, then this method returns
  * false if the input language is not exactly SMT-LIB 2.6.
  */
bool isInputLang_smt2_6(InputLanguage lang, bool exact = false) CVC4_PUBLIC;
bool isOutputLang_smt2_6(OutputLanguage lang, bool exact = false) CVC4_PUBLIC;

InputLanguage toInputLanguage(OutputLanguage language) CVC4_PUBLIC;
OutputLanguage toOutputLanguage(InputLanguage language) CVC4_PUBLIC;
InputLanguage toInputLanguage(std::string language) CVC4_PUBLIC;
OutputLanguage toOutputLanguage(std::string language) CVC4_PUBLIC;

}/* CVC4::language namespace */
}/* CVC4 namespace */

#endif /* CVC4__LANGUAGE_H */
