/*********************                                                        */
/*! \file language.cpp
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

#include "util/language.h"

namespace CVC4 {
namespace language {

InputLanguage toInputLanguage(OutputLanguage language) {
  switch(language) {
  case output::LANG_SMTLIB_V1:
  case output::LANG_SMTLIB_V2:
  case output::LANG_TPTP:
  case output::LANG_CVC4:
    // these entries directly correspond (by design)
    return InputLanguage(int(language));

  default: {
    std::stringstream ss;
    ss << "Cannot map output language `" << language
       << "' to an input language.";
    throw CVC4::Exception(ss.str());
  }
  }/* switch(language) */
}/* toInputLanguage() */

OutputLanguage toOutputLanguage(InputLanguage language) {
  switch(language) {
  case input::LANG_SMTLIB_V1:
  case input::LANG_SMTLIB_V2:
  case input::LANG_CVC4:
  case input::LANG_TPTP:
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
    // initial phase of the main CVC4 driver while it determines which
    // language is appropriate, and during unit tests.  Also, when
    // users are writing their own code against the library.
    return output::LANG_AST;
  }/* switch(language) */
}/* toOutputLanguage() */

}/* CVC4::language namespace */
}/* CVC4 namespace */
