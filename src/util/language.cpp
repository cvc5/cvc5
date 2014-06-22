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
  case output::LANG_Z3STR:
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
  case input::LANG_TPTP:
  case input::LANG_CVC4:
  case input::LANG_Z3STR:
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

OutputLanguage toOutputLanguage(std::string language) {
  if(language == "cvc4" || language == "pl" ||
     language == "presentation" || language == "native" ||
     language == "LANG_CVC4") {
    return output::LANG_CVC4;
  } else if(language == "cvc3" || language == "LANG_CVC3") {
    return output::LANG_CVC3;
  } else if(language == "smtlib1" || language == "smt1" ||
            language == "LANG_SMTLIB_V1") {
    return output::LANG_SMTLIB_V1;
  } else if(language == "smtlib" || language == "smt" ||
            language == "smtlib2" || language == "smt2" ||
            language == "LANG_SMTLIB_V2") {
    return output::LANG_SMTLIB_V2;
  } else if(language == "tptp" || language == "LANG_TPTP") {
    return output::LANG_TPTP;
  } else if(language == "z3str" || language == "z3-str" ||
            language == "LANG_Z3STR") {
    return output::LANG_Z3STR;
  } else if(language == "ast" || language == "LANG_AST") {
    return output::LANG_AST;
  } else if(language == "auto" || language == "LANG_AUTO") {
    return output::LANG_AUTO;
  }

  throw OptionException(std::string("unknown output language `" + language + "'"));
}/* toOutputLanguage() */

InputLanguage toInputLanguage(std::string language) {
  if(language == "cvc4" || language == "pl" ||
     language == "presentation" || language == "native" ||
     language == "LANG_CVC4") {
    return input::LANG_CVC4;
  } else if(language == "smtlib1" || language == "smt1" ||
            language == "LANG_SMTLIB_V1") {
    return input::LANG_SMTLIB_V1;
  } else if(language == "smtlib" || language == "smt" ||
            language == "smtlib2" || language == "smt2" ||
            language == "LANG_SMTLIB_V2") {
    return input::LANG_SMTLIB_V2;
  } else if(language == "tptp" || language == "LANG_TPTP") {
    return input::LANG_TPTP;
  } else if(language == "z3str" || language == "z3-str" ||
            language == "LANG_Z3STR") {
    return input::LANG_Z3STR;
  } else if(language == "auto" || language == "LANG_AUTO") {
    return input::LANG_AUTO;
  }

  throw OptionException(std::string("unknown input language `" + language + "'"));
}/* toInputLanguage() */

}/* CVC4::language namespace */
}/* CVC4 namespace */
