/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of input and output languages.
 */

#include "cvc5_public.h"

#ifndef CVC5__LANGUAGE_H
#define CVC5__LANGUAGE_H

#include <ostream>
#include <string>

#include "cvc5_export.h"

namespace cvc5 {
namespace language {

namespace input {

enum CVC5_EXPORT Language
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

  /** The SMTLIB v2.6 input language, with support for the strings standard */
  LANG_SMTLIB_V2_6 = 0,
  /** Backward-compatibility for enumeration naming */
  LANG_SMTLIB_V2 = LANG_SMTLIB_V2_6,
  /** The TPTP input language */
  LANG_TPTP,
  /** The cvc5 input language */
  LANG_CVC,
  /** The SyGuS input language version 2.0 */
  LANG_SYGUS_V2,

  // START OUTPUT-ONLY LANGUAGES AT ENUM VALUE 10
  // THESE ARE IN PRINCIPLE NOT POSSIBLE INPUT LANGUAGES

  /** LANG_MAX is > any valid InputLanguage id */
  LANG_MAX
}; /* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) CVC5_EXPORT;
inline std::ostream& operator<<(std::ostream& out, Language lang) {
  switch(lang) {
  case LANG_AUTO:
    out << "LANG_AUTO";
    break;
  case LANG_SMTLIB_V2_6:
    out << "LANG_SMTLIB_V2_6";
    break;
  case LANG_TPTP:
    out << "LANG_TPTP";
    break;
  case LANG_CVC: out << "LANG_CVC"; break;
  case LANG_SYGUS_V2: out << "LANG_SYGUS_V2"; break;
  default:
    out << "undefined_input_language";
  }
  return out;
}

}  // namespace input

namespace output {

enum CVC5_EXPORT Language
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

  /** The SMTLIB v2.6 output language, with support for the strings standard */
  LANG_SMTLIB_V2_6 = input::LANG_SMTLIB_V2_6,
  /** Backward-compatibility for enumeration naming */
  LANG_SMTLIB_V2 = input::LANG_SMTLIB_V2,
  /** The TPTP output language */
  LANG_TPTP = input::LANG_TPTP,
  /** The cvc5 output language */
  LANG_CVC = input::LANG_CVC,
  /** The sygus output language version 2.0 */
  LANG_SYGUS_V2 = input::LANG_SYGUS_V2,

  // START OUTPUT-ONLY LANGUAGES AT ENUM VALUE 10
  // THESE ARE IN PRINCIPLE NOT POSSIBLE INPUT LANGUAGES

  /** The AST output language */
  LANG_AST = 10,

  /** LANG_MAX is > any valid OutputLanguage id */
  LANG_MAX
}; /* enum Language */

inline std::ostream& operator<<(std::ostream& out, Language lang) CVC5_EXPORT;
inline std::ostream& operator<<(std::ostream& out, Language lang) {
  switch(lang) {
  case LANG_SMTLIB_V2_6: out << "LANG_SMTLIB_V2_6"; break;
  case LANG_TPTP:
    out << "LANG_TPTP";
    break;
  case LANG_CVC: out << "LANG_CVC"; break;
  case LANG_SYGUS_V2: out << "LANG_SYGUS_V2"; break;
  case LANG_AST:
    out << "LANG_AST";
    break;
  default:
    out << "undefined_output_language";
  }
  return out;
}

}  // namespace output

}  // namespace language

typedef language::input::Language InputLanguage;
typedef language::output::Language OutputLanguage;

namespace language {

/** Is the language a variant of the smtlib version 2 language? */
bool isInputLang_smt2(InputLanguage lang) CVC5_EXPORT;
bool isOutputLang_smt2(OutputLanguage lang) CVC5_EXPORT;

/**
  * Is the language smtlib 2.6 or above? If exact=true, then this method returns
  * false if the input language is not exactly SMT-LIB 2.6.
  */
bool isInputLang_smt2_6(InputLanguage lang, bool exact = false) CVC5_EXPORT;
bool isOutputLang_smt2_6(OutputLanguage lang, bool exact = false) CVC5_EXPORT;

/** Is the language a variant of the SyGuS input language? */
bool isInputLangSygus(InputLanguage lang) CVC5_EXPORT;
bool isOutputLangSygus(OutputLanguage lang) CVC5_EXPORT;

InputLanguage toInputLanguage(OutputLanguage language) CVC5_EXPORT;
OutputLanguage toOutputLanguage(InputLanguage language) CVC5_EXPORT;
InputLanguage toInputLanguage(std::string language) CVC5_EXPORT;
OutputLanguage toOutputLanguage(std::string language) CVC5_EXPORT;

}  // namespace language
}  // namespace cvc5

#endif /* CVC5__LANGUAGE_H */
