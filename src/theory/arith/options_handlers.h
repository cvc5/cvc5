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
 ** \brief Custom handlers and predicates for arithmetic options
 **
 ** Custom handlers and predicates for arithmetic options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__ARITH__OPTIONS_HANDLERS_H

#include <string>

namespace CVC4 {
namespace theory {
namespace arith {

static const std::string arithPresolveLemmasHelp = "\
Presolve lemmas are generated before SAT search begins using the relationship\n\
of constant terms and polynomials.\n\
Modes currently supported by the --arith-presolve-lemmas option:\n\
+ none \n\
+ ineqs \n\
  Outputs lemmas of the general form (<= p c) implies (<= p d) for c < d.\n\
+ eqs \n\
  Outputs lemmas of the general forms\n\
  (= p c) implies (<= p d) for c < d, or\n\
  (= p c) implies (not (= p d)) for c != d.\n\
+ all \n\
  A combination of inequalities and equalities.\n\
";

static const std::string propagationModeHelp = "\
This decides on kind of propagation arithmetic attempts to do during the search.\n\
+ none\n\
+ unate\n\
 use constraints to do unate propagation\n\
+ bi (Bounds Inference)\n\
  infers bounds on basic variables using the upper and lower bounds of the\n\
  non-basic variables in the tableau.\n\
+both\n\
";

static const std::string errorSelectionRulesHelp = "\
This decides on the rule used by simplex during hueristic rounds\n\
for deciding the next basic variable to select.\n\
Heuristic pivot rules available:\n\
+min\n\
  The minimum abs() value of the variable's violation of its bound. (default)\n\
+max\n\
  The maximum violation the bound\n\
+varord\n\
  The variable order\n\
";

inline ArithUnateLemmaMode stringToArithUnateLemmaMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "all") {
    return ALL_PRESOLVE_LEMMAS;
  } else if(optarg == "none") {
    return NO_PRESOLVE_LEMMAS;
  } else if(optarg == "ineqs") {
    return INEQUALITY_PRESOLVE_LEMMAS;
  } else if(optarg == "eqs") {
    return EQUALITY_PRESOLVE_LEMMAS;
  } else if(optarg == "help") {
    puts(arithPresolveLemmasHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --unate-lemmas: `") +
                          optarg + "'.  Try --unate-lemmas help.");
  }
}

inline ArithPropagationMode stringToArithPropagationMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "none") {
    return NO_PROP;
  } else if(optarg == "unate") {
    return UNATE_PROP;
  } else if(optarg == "bi") {
    return BOUND_INFERENCE_PROP;
  } else if(optarg == "both") {
    return BOTH_PROP;
  } else if(optarg == "help") {
    puts(propagationModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --arith-prop: `") +
                          optarg + "'.  Try --arith-prop help.");
  }
}

inline ErrorSelectionRule stringToErrorSelectionRule(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "min") {
    return MINIMUM_AMOUNT;
  } else if(optarg == "varord") {
    return VAR_ORDER;
  } else if(optarg == "max") {
    return MAXIMUM_AMOUNT;
  } else if(optarg == "help") {
    puts(errorSelectionRulesHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --heuristic-pivot-rule: `") +
                          optarg + "'.  Try --heuristic-pivot-rule help.");
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__OPTIONS_HANDLERS_H */
