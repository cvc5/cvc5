/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for TheoryEngine options
 **
 ** Custom handlers and predicates for TheoryEngine options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__OPTIONS_HANDLERS_H

#include "expr/metakind.h"

namespace CVC4 {
namespace theory {

static const std::string theoryOfModeHelp = "\
TheoryOf modes currently supported by the --theoryof-mode option:\n\
\n\
type (default) \n\
+ type variables, constants and equalities by type\n\
\n\
term \n\
+ type variables as uninterpreted, equalities by the parametric theory\n\
";

inline TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg, SmtEngine* smt) {
  if(optarg == "type") {
    return THEORY_OF_TYPE_BASED;
  } else if(optarg == "term") {
    return THEORY_OF_TERM_BASED;
  } else if(optarg == "help") {
    puts(theoryOfModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --theoryof-mode: `") +
                          optarg + "'.  Try --theoryof-mode help.");
  }
}

inline void useTheory(std::string option, std::string optarg, SmtEngine* smt) {
  if(optarg == "help") {
    puts(useTheoryHelp);
    exit(1);
  }
  if(useTheoryValidate(optarg)) {
    std::map<std::string, bool> m = options::theoryAlternates();
    m[optarg] = true;
    options::theoryAlternates.set(m);
  } else {
    throw OptionException(std::string("unknown option for ") + option + ": `" +
                          optarg + "'.  Try --use-theory help.");
  }
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OPTIONS_HANDLERS_H */
