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

#include "options/language.h"

#include <sstream>

#include "base/exception.h"
#include "options/option_exception.h"

namespace cvc5 {
namespace language {

/** define the end points of smt2 languages */
namespace input {
Language LANG_SMTLIB_V2_START = LANG_SMTLIB_V2_6;
Language LANG_SMTLIB_V2_END = LANG_SMTLIB_V2_6;
}
namespace output {
Language LANG_SMTLIB_V2_START = LANG_SMTLIB_V2_6;
Language LANG_SMTLIB_V2_END = LANG_SMTLIB_V2_6;
}

bool isInputLang_smt2(InputLanguage lang)
{
  return lang >= input::LANG_SMTLIB_V2_START
         && lang <= input::LANG_SMTLIB_V2_END;
}

bool isOutputLang_smt2(OutputLanguage lang)
{
  return lang >= output::LANG_SMTLIB_V2_START
         && lang <= output::LANG_SMTLIB_V2_END;
}

bool isInputLang_smt2_6(InputLanguage lang, bool exact)
{
  return exact ? lang == input::LANG_SMTLIB_V2_6
               : (lang >= input::LANG_SMTLIB_V2_6
                  && lang <= input::LANG_SMTLIB_V2_END);
}

bool isOutputLang_smt2_6(OutputLanguage lang, bool exact)
{
  return exact ? lang == output::LANG_SMTLIB_V2_6
               : (lang >= output::LANG_SMTLIB_V2_6
                  && lang <= output::LANG_SMTLIB_V2_END);
}

bool isInputLangSygus(InputLanguage lang)
{
  return lang == input::LANG_SYGUS_V2;
}

bool isOutputLangSygus(OutputLanguage lang)
{
  return lang == output::LANG_SYGUS_V2;
}

InputLanguage toInputLanguage(OutputLanguage language) {
  switch(language) {
  case output::LANG_SMTLIB_V2_6:
  case output::LANG_TPTP:
  case output::LANG_CVC:
  case output::LANG_SYGUS_V2:
    // these entries directly correspond (by design)
    return InputLanguage(int(language));

  default: {
    std::stringstream ss;
    ss << "Cannot map output language `" << language
       << "' to an input language.";
    throw cvc5::Exception(ss.str());
  }
  }/* switch(language) */
}/* toInputLanguage() */

OutputLanguage toOutputLanguage(InputLanguage language) {
  switch(language) {
  case input::LANG_SMTLIB_V2_6:
  case input::LANG_TPTP:
  case input::LANG_CVC:
  case input::LANG_SYGUS_V2:
    // these entries directly correspond (by design)
    return OutputLanguage(int(language));

  default:
    // Revert to the default (AST) language.
    //
    // We used to throw an exception here, but that's not quite right.
    // We often call this while constructing exceptions, for one, and
    // it's better to output SOMETHING related to the original
    // exception rather than mask it with another exception.  Also,
    // the input language isn't always defined---e.g. during the
    // initial phase of the main cvc5 driver while it determines which
    // language is appropriate, and during unit tests.  Also, when
    // users are writing their own code against the library.
    return output::LANG_AST;
  }/* switch(language) */
}/* toOutputLanguage() */

OutputLanguage toOutputLanguage(std::string language)
{
  if (language == "cvc" || language == "pl" || language == "presentation"
      || language == "native" || language == "LANG_CVC")
  {
    return output::LANG_CVC;
  }
  else if (language == "smtlib" || language == "smt" || language == "smtlib2"
           || language == "smt2" || language == "smtlib2.6"
           || language == "smt2.6" || language == "LANG_SMTLIB_V2_6"
           || language == "LANG_SMTLIB_V2")
  {
    return output::LANG_SMTLIB_V2_6;
  }
  else if (language == "tptp" || language == "LANG_TPTP")
  {
    return output::LANG_TPTP;
  }
  else if (language == "sygus" || language == "LANG_SYGUS"
           || language == "sygus2" || language == "LANG_SYGUS_V2")
  {
    return output::LANG_SYGUS_V2;
  }
  else if (language == "ast" || language == "LANG_AST")
  {
    return output::LANG_AST;
  }
  else if (language == "auto" || language == "LANG_AUTO")
  {
    return output::LANG_AUTO;
  }

  throw OptionException(
      std::string("unknown output language `" + language + "'"));
}

InputLanguage toInputLanguage(std::string language) {
  if (language == "cvc" || language == "pl" || language == "presentation"
      || language == "native" || language == "LANG_CVC")
  {
    return input::LANG_CVC;
  }
  else if (language == "smtlib" || language == "smt" || language == "smtlib2"
           || language == "smt2" || language == "smtlib2.6"
           || language == "smt2.6" || language == "LANG_SMTLIB_V2_6"
           || language == "LANG_SMTLIB_V2")
  {
    return input::LANG_SMTLIB_V2_6;
  }
  else if (language == "tptp" || language == "LANG_TPTP")
  {
    return input::LANG_TPTP;
  }
  else if (language == "sygus" || language == "sygus2"
           || language == "LANG_SYGUS" || language == "LANG_SYGUS_V2")
  {
    return input::LANG_SYGUS_V2;
  }
  else if (language == "auto" || language == "LANG_AUTO")
  {
    return input::LANG_AUTO;
  }

  throw OptionException(std::string("unknown input language `" + language + "'"));
}/* toInputLanguage() */

}  // namespace language
}  // namespace cvc5
