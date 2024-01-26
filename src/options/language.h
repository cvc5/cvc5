/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of languages.
 */

#include "cvc5_public.h"

#ifndef CVC5__LANGUAGE_H
#define CVC5__LANGUAGE_H

#include <cvc5/cvc5_export.h>

#include <ostream>
#include <string>

namespace cvc5::internal {

enum class Language
{
  // SPECIAL "NON-LANGUAGE" LANGUAGES HAVE ENUM VALUE < 0

  /** Auto-detect the language */
  LANG_AUTO = -1,

  /** The SMTLIB v2.6 language, with support for the strings standard */
  LANG_SMTLIB_V2_6 = 0,
  /** The SyGuS language version 2.0 */
  LANG_SYGUS_V2,

  /** The AST (output) language */
  LANG_AST,

  /** LANG_MAX is > any valid Language id */
  LANG_MAX
};

std::ostream& operator<<(std::ostream& out, Language lang) CVC5_EXPORT;

namespace language {

/** Is the language a variant of the smtlib version 2 language? */
inline bool isLangSmt2(Language lang)
{
  return lang == Language::LANG_SMTLIB_V2_6;
}

/** Is the language a variant of the SyGuS input language? */
inline bool isLangSygus(Language lang)
{
  return lang == Language::LANG_SYGUS_V2;
}

Language toLanguage(const std::string& language) CVC5_EXPORT;

}  // namespace language
}  // namespace cvc5::internal

#endif /* CVC5__LANGUAGE_H */
