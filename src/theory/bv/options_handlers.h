/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for TheoryBV options
 **
 ** Custom handlers and predicates for TheoryBV options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__BV__OPTIONS_HANDLERS_H

#include "theory/bv/bitblast_mode.h"
#include "main/options.h"

namespace CVC4 {
namespace theory {
namespace bv {

static const std::string bitblastingModeHelp = "\
Bit-blasting modes currently supported by the --bitblast option:\n\
\n\
lazy (default)\n\
+ Separate boolean structure and term reasoning betwen the core\n\
  SAT solver and the bv SAT solver\n\
\n\
eager\n\
+ Bitblast eagerly to bv SAT solver\n\
\n\
aig\n\
+ Bitblast eagerly to bv SAT solver by converting to AIG\n\
";

inline BitblastMode stringToBitblastMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "lazy") {
    if (!options::bitvectorPropagate.wasSetByUser()) {
      options::bitvectorPropagate.set(true);
    }
    if (!options::bitvectorEqualitySolver.wasSetByUser()) {
      options::bitvectorEqualitySolver.set(true);
    }
    if (!options::bitvectorEqualitySlicer.wasSetByUser()) {
      options::bitvectorEqualitySlicer.set(BITVECTOR_SLICER_AUTO);
    }
    if (!options::bitvectorInequalitySolver.wasSetByUser()) {
      options::bitvectorInequalitySolver.set(true);
    }
    if (!options::bitvectorAlgebraicSolver.wasSetByUser()) {
      options::bitvectorAlgebraicSolver.set(true);
    }
    return BITBLAST_MODE_LAZY;
  } else if(optarg == "eager") {
    if (options::produceModels()) {
      throw OptionException(std::string("Eager bit-blasting does not currently support model generation. \n\
                                         Try --bitblast=lazy")); 
    }

    if (!options::bitvectorAig.wasSetByUser()) {
      options::bitvectorAig.set(true);
    }
    if (!options::bitvectorAigSimplifications.wasSetByUser()) {
      options::bitvectorAigSimplifications.set("balance;rewrite");
    }
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }
    return BITBLAST_MODE_EAGER;
  } else if(optarg == "help") {
    puts(bitblastingModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bitblast: `") +
                          optarg + "'.  Try --bitblast=help.");
  }
}

static const std::string bvSlicerModeHelp = "\
Bit-vector equality slicer modes supported by the --bv-eq-slicer option:\n\
\n\
auto (default)\n\
+ Turn slicer on if input has only equalities over core symbols\n\
\n\
on\n\
+ Turn slicer on\n\
\n\
off\n\
+ Turn slicer off\n\
";

inline BvSlicerMode stringToBvSlicerMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {

  if(optarg == "auto") {
    return BITVECTOR_SLICER_AUTO;
  } else if(optarg == "on") {
    return BITVECTOR_SLICER_ON;
  } else if(optarg == "off") {
    return BITVECTOR_SLICER_OFF; 
  } else if(optarg == "help") {
    puts(bitblastingModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bv-eq-slicer: `") +
                          optarg + "'.  Try --bv-eq-slicer=help.");
  }
}

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__OPTIONS_HANDLERS_H */
