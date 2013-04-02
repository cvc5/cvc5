/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__QUANTIFIERS__OPTIONS_HANDLERS_H

#include <string>

namespace CVC4 {
namespace theory {
namespace quantifiers {

static const std::string instWhenHelp = "\
Modes currently supported by the --inst-when option:\n\
\n\
full (default)\n\
+ Run instantiation round at full effort, before theory combination.\n\
\n\
full-last-call\n\
+ Alternate running instantiation rounds at full effort and last\n\
  call.  In other words, interleave instantiation and theory combination.\n\
\n\
last-call\n\
+ Run instantiation at last call effort, after theory combination.\n\
\n\
";

static const std::string literalMatchHelp = "\
Literal match modes currently supported by the --literal-match option:\n\
\n\
none (default)\n\
+ Do not use literal matching.\n\
\n\
predicate\n\
+ Consider the phase requirements of predicate literals when applying heuristic\n\
  quantifier instantiation.  For example, the trigger P( x ) in the quantified \n\
  formula forall( x ). ( P( x ) V ~Q( x ) ) will only be matched with ground\n\
  terms P( t ) where P( t ) is in the equivalence class of false, and likewise\n\
  Q( x ) with Q( s ) where Q( s ) is in the equivalence class of true.\n\
\n\
";

static const std::string axiomInstModeHelp = "\
Axiom instantiation modes currently supported by the --axiom-inst option:\n\
\n\
default \n\
+ Treat axioms the same as usual quantifiers, i.e. use all available methods for\n\
  instantiating axioms.\n\
\n\
trust \n\
+ Treat axioms only using heuristic instantiation.  Return unknown if in the case\n\
  that no instantiations are produced.\n\
\n\
priority \n\
+ Treat axioms only using heuristic instantiation.  Resort to using all methods\n\
  in the case that no instantiations are produced.\n\
\n\
";

inline InstWhenMode stringToInstWhenMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "pre-full") {
    return INST_WHEN_PRE_FULL;
  } else if(optarg == "full") {
    return INST_WHEN_FULL;
  } else if(optarg == "full-last-call") {
    return INST_WHEN_FULL_LAST_CALL;
  } else if(optarg == "last-call") {
    return INST_WHEN_LAST_CALL;
  } else if(optarg == "help") {
    puts(instWhenHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-when: `") +
                          optarg + "'.  Try --inst-when help.");
  }
}

inline void checkInstWhenMode(std::string option, InstWhenMode mode, SmtEngine* smt) throw(OptionException) {
  if(mode == INST_WHEN_PRE_FULL) {
    throw OptionException(std::string("Mode pre-full for ") + option + " is not supported in this release.");
  }
}

inline LiteralMatchMode stringToLiteralMatchMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg ==  "none") {
    return LITERAL_MATCH_NONE;
  } else if(optarg ==  "predicate") {
    return LITERAL_MATCH_PREDICATE;
  } else if(optarg ==  "equality") {
    return LITERAL_MATCH_EQUALITY;
  } else if(optarg ==  "help") {
    puts(literalMatchHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --literal-matching: `") +
                          optarg + "'.  Try --literal-matching help.");
  }
}

inline void checkLiteralMatchMode(std::string option, LiteralMatchMode mode, SmtEngine* smt) throw(OptionException) {
  if(mode == LITERAL_MATCH_EQUALITY) {
    throw OptionException(std::string("Mode equality for ") + option + " is not supported in this release.");
  }
}

inline AxiomInstMode stringToAxiomInstMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg ==  "default") {
    return AXIOM_INST_MODE_DEFAULT;
  } else if(optarg ==  "trust") {
    return AXIOM_INST_MODE_TRUST;
  } else if(optarg ==  "priority") {
    return AXIOM_INST_MODE_PRIORITY;
  } else if(optarg ==  "help") {
    puts(axiomInstModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --axiom-inst: `") +
                          optarg + "'.  Try --axiom-inst help.");
  }
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__OPTIONS_HANDLERS_H */
