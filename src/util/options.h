/*********************                                                        */
/*! \file options.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, cconway
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT.
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS_H
#define __CVC4__OPTIONS_H

#include <iostream>
#include <fstream>
#include <string>

#include "util/exception.h"
#include "util/language.h"
#include "util/tls.h"

namespace CVC4 {

class ExprStream;

/** Class representing an option-parsing exception. */
class CVC4_PUBLIC OptionException : public CVC4::Exception {
public:
    OptionException(const std::string& s) throw() :
      CVC4::Exception("Error in option parsing: " + s) {
    }
};/* class OptionException */

struct CVC4_PUBLIC Options {

  /** The current Options in effect */
  static CVC4_THREADLOCAL(const Options*) s_current;

  /** Get the current Options in effect */
  static inline const Options* current() {
    return s_current;
  }

  /** The name of the binary (e.g. "cvc4") */
  std::string binary_name;

  /** Whether to collect statistics during this run */
  bool statistics;

  std::istream* in; /*< The input stream to use */
  std::ostream* out; /*< The output stream to use */
  std::ostream* err; /*< The error stream to use */

  /* -1 means no output */
  /* 0 is normal (and default) -- warnings only */
  /* 1 is warnings + notices so the user doesn't get too bored */
  /* 2 is chatty, giving statistical things etc. */
  /* with 3, the solver is slowed down by all the scrolling */
  int verbosity;

  /** The input language */
  InputLanguage inputLanguage;

  /** The output language */
  OutputLanguage outputLanguage;

  /** Should we print the help message? */
  bool help;

  /** Should we print the release information? */
  bool version;

  /** Should we print the language help information? */
  bool languageHelp;

  /** Should we exit after parsing? */
  bool parseOnly;

  /** Should we exit after preprocessing? */
  bool preprocessOnly;

  /** Should the parser do semantic checks? */
  bool semanticChecks;

  /** Should the TheoryEngine do theory registration? */
  bool theoryRegistration;

  /** Should the parser memory-map file input? */
  bool memoryMap;

  /** Should we strictly enforce the language standard while parsing? */
  bool strictParsing;

  /** Should we expand function definitions lazily? */
  bool lazyDefinitionExpansion;

  /** Enumeration of simplification modes (when to simplify). */
  typedef enum {
    /** Simplify the assertions as they come in */
    SIMPLIFICATION_MODE_INCREMENTAL,
    /** Simplify the assertions all together once a check is requested */
    SIMPLIFICATION_MODE_BATCH,
    /** Don't do simplification */
    SIMPLIFICATION_MODE_NONE
  } SimplificationMode;

  /** When/whether to perform nonclausal simplifications. */
  SimplificationMode simplificationMode;

  /** Whether to perform the static learning pass. */
  bool doStaticLearning;

  /** Whether we're in interactive mode or not */
  bool interactive;

  /**
   * Whether we're in interactive mode (or not) due to explicit user
   * setting (if false, we inferred the proper default setting).
   */
  bool interactiveSetByUser;

  /** Whether we should "spin" on a SIG_SEGV. */
  bool segvNoSpin;

  /** Whether we support SmtEngine::getValue() for this run. */
  bool produceModels;

  /** Whether we support SmtEngine::getAssignment() for this run. */
  bool produceAssignments;

  /** Whether we do typechecking at all. */
  bool typeChecking;

  /** Whether we do typechecking at Expr creation time. */
  bool earlyTypeChecking;

  /** Whether incemental solving (push/pop) */
  bool incrementalSolving;

  /** Replay file to use (for decisions); empty if no replay file. */
  std::string replayFilename;

  /** Replay stream to use (for decisions); NULL if no replay file. */
  ExprStream* replayStream;

  /** Log to write replay instructions to; NULL if not logging. */
  std::ostream* replayLog;

  /** Determines whether arithmetic will try to variables. */
  bool variableRemovalEnabled;

  /** Turn on and of arithmetic propagation. */
  bool arithPropagation;

  /**
   * Frequency for the sat solver to make random decisions.
   * Should be between 0 and 1.
   */
  double satRandomFreq;

  /**
   * Seed for Minisat's random decision procedure.
   * If this is 0, no random decisions will occur.
   **/
  double satRandomSeed;

  /** The pivot rule for arithmetic */
  typedef enum { MINIMUM, BREAK_TIES, MAXIMUM } ArithPivotRule;
  ArithPivotRule pivotRule;

  /**
   * The number of pivots before Bland's pivot rule is used on a basic
   * variable in arithmetic.
   */
  uint16_t arithPivotThreshold;

  /**
   * The maximum row length that arithmetic will use for propagation.
   */
  uint16_t arithPropagateMaxLength;

  /**
   * Whether to do the symmetry-breaking preprocessing in UF as
   * described by Deharbe et al. in CADE 2011 (on by default).
   */
  bool ufSymmetryBreaker;

  Options();

  /**
   * Get a description of the command-line flags accepted by
   * parseOptions.  The returned string will be escaped so that it is
   * suitable as an argument to printf. */
  std::string getDescription() const;

  /**
   * Print overall command-line option usage message, prefixed by
   * "msg"---which could be an error message causing the usage
   * output in the first place, e.g. "no such option --foo"
   */
  static void printUsage(const std::string msg, std::ostream& out);

  /** Print help for the --lang command line option */
  static void printLanguageHelp(std::ostream& out);

  /**
   * Initialize the options based on the given command-line arguments.
   */
  int parseOptions(int argc, char* argv[]) throw(OptionException);

  /**
   * Set the output language based on the given string.
   */
  void setOutputLanguage(const char* str) throw(OptionException);

  /**
   * Set the input language based on the given string.
   */
  void setInputLanguage(const char* str) throw(OptionException);

};/* struct Options */

inline std::ostream& operator<<(std::ostream& out,
                                Options::SimplificationMode mode) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out,
                                Options::SimplificationMode mode) {
  switch(mode) {
  case Options::SIMPLIFICATION_MODE_INCREMENTAL:
    out << "SIMPLIFICATION_MODE_INCREMENTAL";
    break;
  case Options::SIMPLIFICATION_MODE_BATCH:
    out << "SIMPLIFICATION_MODE_BATCH";
    break;
  case Options::SIMPLIFICATION_MODE_NONE:
    out << "SIMPLIFICATION_MODE_NONE";
    break;
  default:
    out << "SimplificationMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, Options::ArithPivotRule rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS_H */
