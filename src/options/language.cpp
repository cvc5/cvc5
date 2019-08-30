/*********************                                                        */
/*! \file language.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Andres Noetzli
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

#include "options/language.h"

namespace CVC4 {
namespace language {

/** define the end points of smt2 languages */
namespace input {
Language LANG_SMTLIB_V2_END = LANG_SMTLIB_V2_6_1;
}
namespace output {
Language LANG_SMTLIB_V2_END = LANG_SMTLIB_V2_6_1;
}

bool isInputLang_smt2(InputLanguage lang)
{
  return (lang >= input::LANG_SMTLIB_V2_0 && lang <= input::LANG_SMTLIB_V2_END)
         || lang == input::LANG_Z3STR;
}

bool isOutputLang_smt2(OutputLanguage lang)
{
  return (lang >= output::LANG_SMTLIB_V2_0
          && lang <= output::LANG_SMTLIB_V2_END)
         || lang == output::LANG_Z3STR;
}

bool isInputLang_smt2_5(InputLanguage lang, bool exact)
{
  return exact ? lang == input::LANG_SMTLIB_V2_5
               : (lang >= input::LANG_SMTLIB_V2_5
                  && lang <= input::LANG_SMTLIB_V2_END);
}

bool isOutputLang_smt2_5(OutputLanguage lang, bool exact)
{
  return exact ? lang == output::LANG_SMTLIB_V2_5
               : (lang >= output::LANG_SMTLIB_V2_5
                  && lang <= output::LANG_SMTLIB_V2_END);
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

InputLanguage toInputLanguage(OutputLanguage language) {
  switch(language) {
  case output::LANG_SMTLIB_V1:
  case output::LANG_SMTLIB_V2_0:
  case output::LANG_SMTLIB_V2_5:
  case output::LANG_SMTLIB_V2_6:
  case output::LANG_SMTLIB_V2_6_1:
  case output::LANG_TPTP:
  case output::LANG_CVC4:
  case output::LANG_Z3STR:
  case output::LANG_SYGUS:
  case output::LANG_SYGUS_V2:
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
    return OutputLanguage(output::LANG_SMTLIB_V2_0);
  case input::LANG_SMTLIB_V2_0:
  case input::LANG_SMTLIB_V2_5:
  case input::LANG_SMTLIB_V2_6:
  case input::LANG_SMTLIB_V2_6_1:
  case input::LANG_TPTP:
  case input::LANG_CVC4:
  case input::LANG_Z3STR:
  case input::LANG_SYGUS:
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
  }
  else if (language == "smtlib2.0" || language == "smt2.0"
           || language == "LANG_SMTLIB_V2_0")
  {
    return output::LANG_SMTLIB_V2_0;
  } else if(language == "smtlib2.5" || language == "smt2.5" ||
            language == "LANG_SMTLIB_V2_5") {
    return output::LANG_SMTLIB_V2_5;
  }
  else if (language == "smtlib" || language == "smt" || language == "smtlib2"
           || language == "smt2" || language == "smtlib2.6"
           || language == "smt2.6" || language == "LANG_SMTLIB_V2_6"
           || language == "LANG_SMTLIB_V2")
  {
    return output::LANG_SMTLIB_V2_6;
  }
  else if (language == "smtlib2.6.1" || language == "smt2.6.1"
           || language == "LANG_SMTLIB_V2_6_1")
  {
    return output::LANG_SMTLIB_V2_6_1;
  } else if(language == "tptp" || language == "LANG_TPTP") {
    return output::LANG_TPTP;
  } else if(language == "z3str" || language == "z3-str" ||
            language == "LANG_Z3STR") {
    return output::LANG_Z3STR;
  } else if(language == "sygus" || language == "LANG_SYGUS") {
    return output::LANG_SYGUS;
  }
  else if (language == "sygus2" || language == "LANG_SYGUS_V2")
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
  } else if(language == "smtlib2.0" || language == "smt2.0" ||
            language == "LANG_SMTLIB_V2_0") {
    return input::LANG_SMTLIB_V2_0;
  } else if(language == "smtlib2.5" || language == "smt2.5" ||
            language == "LANG_SMTLIB_V2_5") {
    return input::LANG_SMTLIB_V2_5;
  } else if(language == "smtlib" || language == "smt" ||
            language == "smtlib2" || language == "smt2" ||
            language == "smtlib2.6" || language == "smt2.6" ||
            language == "LANG_SMTLIB_V2_6" || language == "LANG_SMTLIB_V2") {
    return input::LANG_SMTLIB_V2_6;
  }
  else if (language == "smtlib2.6.1" || language == "smt2.6.1"
           || language == "LANG_SMTLIB_V2_6_1")
  {
    return input::LANG_SMTLIB_V2_6_1;
  } else if(language == "tptp" || language == "LANG_TPTP") {
    return input::LANG_TPTP;
  } else if(language == "z3str" || language == "z3-str" ||
            language == "LANG_Z3STR") {
    return input::LANG_Z3STR;
  } else if(language == "sygus" || language == "LANG_SYGUS") {
    return input::LANG_SYGUS;
  }
  else if (language == "sygus2" || language == "LANG_SYGUS_V2")
  {
    return input::LANG_SYGUS_V2;
  }
  else if (language == "auto" || language == "LANG_AUTO")
  {
    return input::LANG_AUTO;
  }

  throw OptionException(std::string("unknown input language `" + language + "'"));
}/* toInputLanguage() */

}/* CVC4::language namespace */
}/* CVC4 namespace */
