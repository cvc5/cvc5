/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
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

inline void abcEnabledBuild(std::string option, bool value, SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

inline void abcEnabledBuild(std::string option, std::string value, SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(!value.empty()) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

inline void satSolverEnabledBuild(std::string option,
				  SatSolverMode solver,
				  SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_USE_CRYPTOMINISAT
  if(solver == SAT_SOLVER_CRYPTOMINISAT) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an cryptominisat-enabled build of CVC4; this binary was not built with cryptominisat support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_CRYPTOMINISAT */

#ifndef CVC4_USE_GLUCOSE
  if(solver == SAT_SOLVER_GLUCOSE) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an glucose-enabled build of CVC4; this binary was not built with glucose support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_GLUCOSE */
  
#ifndef CVC4_USE_RISS
  if(solver == SAT_SOLVER_RISS) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an riss-enabled build of CVC4; this binary was not built with riss support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_RISS */

}
 
 
static const std::string bitblastingModeHelp = "\
Bit-blasting modes currently supported by the --bitblast option:\n\
\n\
lazy (default)\n\
+ Separate boolean structure and term reasoning betwen the core\n\
  SAT solver and the bv SAT solver\n\
\n\
eager\n\
+ Bitblast eagerly to bv SAT solver\n\
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
      if (options::incrementalSolving() ||
          options::produceModels()) {
        options::bitvectorEqualitySlicer.set(BITVECTOR_SLICER_OFF);
      } else {
        options::bitvectorEqualitySlicer.set(BITVECTOR_SLICER_AUTO);
      }
    }
    
    if (!options::bitvectorInequalitySolver.wasSetByUser()) {
      options::bitvectorInequalitySolver.set(true);
    }
    if (!options::bitvectorAlgebraicSolver.wasSetByUser()) {
      options::bitvectorAlgebraicSolver.set(true);
    }
    return BITBLAST_MODE_LAZY;
  } else if(optarg == "eager") {

    if (options::incrementalSolving() &&
        options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Eager bit-blasting does not currently support incremental mode. \n\
                                         Try --bitblast=lazy"));
    }
    
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }

    if (!options::bvAbstraction.wasSetByUser() &&
        !options::skolemizeArguments.wasSetByUser()) {
      options::bvAbstraction.set(true);
      options::skolemizeArguments.set(true); 
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

inline void setBitblastAig(std::string option, bool arg, SmtEngine* smt) throw(OptionException) {
  if(arg) {
    if(options::bitblastMode.wasSetByUser()) {
      if(options::bitblastMode() != BITBLAST_MODE_EAGER) {
        throw OptionException("bitblast-aig must be used with eager bitblaster");
      }
    } else {
      options::bitblastMode.set(stringToBitblastMode("", "eager", smt));
    }
    if(!options::bitvectorAigSimplifications.wasSetByUser()) {
      options::bitvectorAigSimplifications.set("balance;drw");
    }
  }
}

static const std::string bvSatSolverHelp = "\
Sat solvers currently supported by the --bv-sat-solver option:\n\
\n\
minisat (default)\n\
\n\
cryptominisat\n\
\n\
riss\n\
\n\
glucose\n\
";

inline SatSolverMode stringToSatSolver(std::string option,
				       std::string optarg,
				       SmtEngine* smt) throw(OptionException) {
  if(optarg == "minisat") {
    return SAT_SOLVER_MINISAT;
  } else if(optarg == "cryptominisat") {

    if (options::incrementalSolving() &&
        options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Cryptominsat does not support incremental mode. \n\
                                         Try --bv-sat-solver=minisat"));
    }

    if (options::bitblastMode() == BITBLAST_MODE_LAZY &&
        options::bitblastMode.wasSetByUser()) {
      throw OptionException(std::string("Cryptominsat does not support lazy bit-blsating. \n\
                                         Try --bv-sat-solver=minisat"));
    }
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }

    if (!options::bvAbstraction.wasSetByUser() &&
        !options::skolemizeArguments.wasSetByUser()) {
      options::bvAbstraction.set(true);
      options::skolemizeArguments.set(true); 
    }
    return SAT_SOLVER_CRYPTOMINISAT;
  } else if(optarg == "riss") {

    if (options::incrementalSolving() &&
        options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Riss does not support incremental mode. \n\
                                         Try --bv-sat-solver=minisat"));
    }

    if (options::bitblastMode() == BITBLAST_MODE_LAZY &&
        options::bitblastMode.wasSetByUser()) {
      throw OptionException(std::string("Riss does not support lazy bit-blsating. \n\
                                         Try --bv-sat-solver=minisat"));
    }
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }

    if (!options::bvAbstraction.wasSetByUser() &&
        !options::skolemizeArguments.wasSetByUser()) {
      options::bvAbstraction.set(true);
      options::skolemizeArguments.set(true); 
    }
    return SAT_SOLVER_RISS;
  }else if(optarg == "glucose") {

    if (options::incrementalSolving() &&
        options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Glucose does not support incremental mode. \n\
                                         Try --bv-sat-solver=minisat"));
    }

    if (options::bitblastMode() == BITBLAST_MODE_LAZY &&
        options::bitblastMode.wasSetByUser()) {
      throw OptionException(std::string("Glucose does not support lazy bit-blsating. \n\
                                         Try --bv-sat-solver=minisat"));
    }
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }

    if (!options::bvAbstraction.wasSetByUser() &&
        !options::skolemizeArguments.wasSetByUser()) {
      options::bvAbstraction.set(true);
      options::skolemizeArguments.set(true); 
    }
    return SAT_SOLVER_GLUCOSE;
  } else if(optarg == "help") {
    puts(bvSatSolverHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bv-sat-solver: `") +
                          optarg + "'.  Try --bv-sat-solver=help.");
  }
}
 
 
}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__OPTIONS_HANDLERS_H */
