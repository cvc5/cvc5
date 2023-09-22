/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of input and output languages.
 */

#include "options/language.h"

#include "options/option_exception.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, Language lang)
{
  switch (lang)
  {
    case Language::LANG_AUTO: out << "LANG_AUTO"; break;
    case Language::LANG_SMTLIB_V2_6: out << "LANG_SMTLIB_V2_6"; break;
    case Language::LANG_SYGUS_V2: out << "LANG_SYGUS_V2"; break;
    default: out << "undefined_language";
  }
  return out;
}

namespace language {

Language toLanguage(const std::string& language)
{
  if (language == "smtlib" || language == "smt" || language == "smtlib2"
      || language == "smt2" || language == "smtlib2.6" || language == "smt2.6"
      || language == "LANG_SMTLIB_V2_6" || language == "LANG_SMTLIB_V2")
  {
    return Language::LANG_SMTLIB_V2_6;
  }
  else if (language == "sygus" || language == "LANG_SYGUS"
           || language == "sygus2" || language == "LANG_SYGUS_V2")
  {
    return Language::LANG_SYGUS_V2;
  }
  else if (language == "ast" || language == "LANG_AST")
  {
    return Language::LANG_AST;
  }
  else if (language == "auto" || language == "LANG_AUTO")
  {
    return Language::LANG_AUTO;
  }

  throw OptionException(std::string("unknown language `" + language + "'"));
}

}  // namespace language
}  // namespace cvc5::internal
