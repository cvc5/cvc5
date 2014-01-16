/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for SmtEngine options
 **
 ** Custom handlers and predicates for SmtEngine options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SMT__OPTIONS_HANDLERS_H
#define __CVC4__SMT__OPTIONS_HANDLERS_H

#include "cvc4autoconfig.h"
#include "util/dump.h"
#include "smt/modal_exception.h"
#include "smt/smt_engine.h"
#include "lib/strtok_r.h"

#include <cerrno>
#include <cstring>
#include <sstream>

namespace CVC4 {
namespace smt {

static inline std::string __cvc4_errno_failreason() {
#if HAVE_STRERROR_R
#if STRERROR_R_CHAR_P
  if(errno != 0) {
    // GNU version of strerror_r: *might* use the given buffer,
    // or might not.  It returns a pointer to buf, or not.
    char buf[80];
    return std::string(strerror_r(errno, buf, sizeof buf));
  } else {
    return "unknown reason";
  }
#else /* STRERROR_R_CHAR_P */
  if(errno != 0) {
    // XSI version of strerror_r: always uses the given buffer.
    // Returns an error code.
    char buf[80];
    if(strerror_r(errno, buf, sizeof buf) == 0) {
      return std::string(buf);
    } else {
      // some error occurred while getting the error string
      return "unknown reason";
    }
  } else {
    return "unknown reason";
  }
#endif /* STRERROR_R_CHAR_P */
#else /* HAVE_STRERROR_R */
  return "unknown reason";
#endif /* HAVE_STRERROR_R */
}

static const std::string dumpHelp = "\
Dump modes currently supported by the --dump option:\n\
\n\
benchmark\n\
+ Dump the benchmark structure (set-logic, push/pop, queries, etc.), but\n\
  does not include any declarations or assertions.  Implied by all following\n\
  modes.\n\
\n\
declarations\n\
+ Dump user declarations.  Implied by all following modes.\n\
\n\
skolems\n\
+ Dump internally-created skolem variable declarations.  These can\n\
  arise from preprocessing simplifications, existential elimination,\n\
  and a number of other things.  Implied by all following modes.\n\
\n\
assertions\n\
+ Output the assertions after preprocessing and before clausification.\n\
  Can also specify \"assertions:pre-PASS\" or \"assertions:post-PASS\",\n\
  where PASS is one of the preprocessing passes: definition-expansion\n\
  boolean-terms constrain-subtypes substitution skolem-quant simplify\n\
  static-learning ite-removal repeat-simplify rewrite-apply-to-const\n\
  theory-preprocessing.\n\
  PASS can also be the special value \"everything\", in which case the\n\
  assertions are printed before any preprocessing (with\n\
  \"assertions:pre-everything\") or after all preprocessing completes\n\
  (with \"assertions:post-everything\").\n\
\n\
clauses\n\
+ Do all the preprocessing outlined above, and dump the CNF-converted\n\
  output\n\
\n\
state\n\
+ Dump all contextual assertions (e.g., SAT decisions, propagations..).\n\
  Implied by all \"stateful\" modes below and conflicts with all\n\
  non-stateful modes below.\n\
\n\
t-conflicts [non-stateful]\n\
+ Output correctness queries for all theory conflicts\n\
\n\
missed-t-conflicts [stateful]\n\
+ Output completeness queries for theory conflicts\n\
\n\
t-propagations [stateful]\n\
+ Output correctness queries for all theory propagations\n\
\n\
missed-t-propagations [stateful]\n\
+ Output completeness queries for theory propagations (LARGE and EXPENSIVE)\n\
\n\
t-lemmas [non-stateful]\n\
+ Output correctness queries for all theory lemmas\n\
\n\
t-explanations [non-stateful]\n\
+ Output correctness queries for all theory explanations\n\
\n\
bv-rewrites [non-stateful]\n\
+ Output correctness queries for all bitvector rewrites\n\
\n\
theory::fullcheck [non-stateful]\n\
+ Output completeness queries for all full-check effort-level theory checks\n\
\n\
Dump modes can be combined with multiple uses of --dump.  Generally you want\n\
one from the assertions category (either assertions or clauses), and\n\
perhaps one or more stateful or non-stateful modes for checking correctness\n\
and completeness of decision procedure implementations.  Stateful modes dump\n\
the contextual assertions made by the core solver (all decisions and\n\
propagations as assertions; that affects the validity of the resulting\n\
correctness and completeness queries, so of course stateful and non-stateful\n\
modes cannot be mixed in the same run.\n\
\n\
The --output-language option controls the language used for dumping, and\n\
this allows you to connect CVC4 to another solver implementation via a UNIX\n\
pipe to perform on-line checking.  The --dump-to option can be used to dump\n\
to a file.\n\
";

static const std::string simplificationHelp = "\
Simplification modes currently supported by the --simplification option:\n\
\n\
batch (default) \n\
+ save up all ASSERTions; run nonclausal simplification and clausal\n\
  (MiniSat) propagation for all of them only after reaching a querying command\n\
  (CHECKSAT or QUERY or predicate SUBTYPE declaration)\n\
\n\
incremental\n\
+ run nonclausal simplification and clausal propagation at each ASSERT\n\
  (and at CHECKSAT/QUERY/SUBTYPE)\n\
\n\
none\n\
+ do not perform nonclausal simplification\n\
";

inline void dumpMode(std::string option, std::string optarg, SmtEngine* smt) {
#ifdef CVC4_DUMPING
  char* optargPtr = strdup(optarg.c_str());
  char* tokstr = optargPtr;
  char* toksave;
  while((optargPtr = strtok_r(tokstr, ",", &toksave)) != NULL) {
    tokstr = NULL;
    if(!strcmp(optargPtr, "benchmark")) {
    } else if(!strcmp(optargPtr, "declarations")) {
    } else if(!strcmp(optargPtr, "assertions")) {
      Dump.on("assertions:post-everything");
    } else if(!strncmp(optargPtr, "assertions:", 11)) {
      const char* p = optargPtr + 11;
      if(!strncmp(p, "pre-", 4)) {
        p += 4;
      } else if(!strncmp(p, "post-", 5)) {
        p += 5;
      } else {
        throw OptionException(std::string("don't know how to dump `") +
                              optargPtr + "'.  Please consult --dump help.");
      }
      if(!strcmp(p, "everything")) {
      } else if(!strcmp(p, "definition-expansion")) {
      } else if(!strcmp(p, "boolean-terms")) {
      } else if(!strcmp(p, "constrain-subtypes")) {
      } else if(!strcmp(p, "substitution")) {
      } else if(!strcmp(p, "skolem-quant")) {
      } else if(!strcmp(p, "simplify")) {
      } else if(!strcmp(p, "static-learning")) {
      } else if(!strcmp(p, "ite-removal")) {
      } else if(!strcmp(p, "repeat-simplify")) {
      } else if(!strcmp(p, "rewrite-apply-to-const")) {
      } else if(!strcmp(p, "theory-preprocessing")) {
      } else if(!strcmp(p, "nonclausal")) {
      } else if(!strcmp(p, "theorypp")) {
      } else if(!strcmp(p, "itesimp")) {
      } else if(!strcmp(p, "unconstrained")) {
      } else if(!strcmp(p, "repeatsimp")) {
      } else {
        throw OptionException(std::string("don't know how to dump `") +
                              optargPtr + "'.  Please consult --dump help.");
      }
      Dump.on("assertions");
    } else if(!strcmp(optargPtr, "skolems")) {
    } else if(!strcmp(optargPtr, "clauses")) {
    } else if(!strcmp(optargPtr, "t-conflicts") ||
              !strcmp(optargPtr, "t-lemmas") ||
              !strcmp(optargPtr, "t-explanations") ||
              !strcmp(optargPtr, "bv-rewrites") ||
              !strcmp(optargPtr, "theory::fullcheck")) {
      // These are "non-state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is dumped, it will interfere with the validity
      // of these generated queries.
      if(Dump.isOn("state")) {
        throw OptionException(std::string("dump option `") + optargPtr +
                              "' conflicts with a previous, "
                              "state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("no-permit-state");
      }
    } else if(!strcmp(optargPtr, "state") ||
              !strcmp(optargPtr, "missed-t-conflicts") ||
              !strcmp(optargPtr, "t-propagations") ||
              !strcmp(optargPtr, "missed-t-propagations")) {
      // These are "state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is not dumped, it will interfere with the
      // validity of these generated queries.
      if(Dump.isOn("no-permit-state")) {
        throw OptionException(std::string("dump option `") + optargPtr +
                              "' conflicts with a previous, "
                              "non-state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("state");
      }
    } else if(!strcmp(optargPtr, "help")) {
      puts(dumpHelp.c_str());
      exit(1);
    } else {
      throw OptionException(std::string("unknown option for --dump: `") +
                            optargPtr + "'.  Try --dump help.");
    }

    Dump.on(optargPtr);
    Dump.on("benchmark");
    if(strcmp(optargPtr, "benchmark")) {
      Dump.on("declarations");
      if(strcmp(optargPtr, "declarations")) {
        Dump.on("skolems");
      }
    }
  }
  free(optargPtr);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline SimplificationMode stringToSimplificationMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "batch") {
    return SIMPLIFICATION_MODE_BATCH;
  } else if(optarg == "incremental") {
    return SIMPLIFICATION_MODE_INCREMENTAL;
  } else if(optarg == "none") {
    return SIMPLIFICATION_MODE_NONE;
  } else if(optarg == "help") {
    puts(simplificationHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --simplification: `") +
                          optarg + "'.  Try --simplification help.");
  }
}

// ensure we haven't started search yet
inline void beforeSearch(std::string option, bool value, SmtEngine* smt) throw(ModalException) {
  if(smt != NULL && smt->d_fullyInited) {
    std::stringstream ss;
    ss << "cannot change option `" << option << "' after final initialization (i.e., after logic has been set)";
    throw ModalException(ss.str());
  }
}

// ensure we are a proof-enabled build of CVC4
inline void proofEnabledBuild(std::string option, bool value, SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_PROOF
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a proofs-enabled build of CVC4; this binary was not built with proof support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_PROOF */
}

inline void unsatCoresEnabledBuild(std::string option, bool value, SmtEngine* smt) throw(OptionException) {
  if(value) {
    throw UnrecognizedOptionException("CVC4 does not yet have support for unsatisfiable cores");
  }
}

// This macro is used for setting :regular-output-channel and :diagnostic-output-channel
// to redirect a stream.  It maintains all attributes set on the stream.
#define __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(__channel_get, __channel_set) \
  { \
    int dagSetting = expr::ExprDag::getDag(__channel_get); \
    size_t exprDepthSetting = expr::ExprSetDepth::getDepth(__channel_get); \
    bool printtypesSetting = expr::ExprPrintTypes::getPrintTypes(__channel_get); \
    OutputLanguage languageSetting = expr::ExprSetLanguage::getLanguage(__channel_get); \
    __channel_set; \
    __channel_get << Expr::dag(dagSetting); \
    __channel_get << Expr::setdepth(exprDepthSetting); \
    __channel_get << Expr::printtypes(printtypesSetting); \
    __channel_get << Expr::setlanguage(languageSetting); \
  }

inline void dumpToFile(std::string option, std::string optarg, SmtEngine* smt) {
#ifdef CVC4_DUMPING
  std::ostream* outStream = NULL;
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --dump-to"));
  } else if(optarg == "-") {
    outStream = &DumpOutC::dump_cout;
  } else {
    errno = 0;
    outStream = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open dump-to file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
  }
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Dump.getStream(), Dump.setStream(*outStream));
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline void setRegularOutputChannel(std::string option, std::string optarg, SmtEngine* smt) {
  std::ostream* outStream = NULL;
  if(optarg == "") {
    throw OptionException(std::string("Bad file name setting for regular output channel"));
  } else if(optarg == "stdout") {
    outStream = &std::cout;
  } else if(optarg == "stderr") {
    outStream = &std::cerr;
  } else {
    errno = 0;
    outStream = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open regular-output-channel file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
  }
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(*options::err(), options::err.set(outStream));
}

inline void setDiagnosticOutputChannel(std::string option, std::string optarg, SmtEngine* smt) {
  std::ostream* outStream = NULL;
  if(optarg == "") {
    throw OptionException(std::string("Bad file name setting for diagnostic output channel"));
  } else if(optarg == "stdout") {
    outStream = &std::cout;
  } else if(optarg == "stderr") {
    outStream = &std::cerr;
  } else {
    errno = 0;
    outStream = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open diagnostic-output-channel file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
  }
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Debug.getStream(), Debug.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Warning.getStream(), Warning.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Message.getStream(), Message.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Notice.getStream(), Notice.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Chat.getStream(), Chat.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Trace.getStream(), Trace.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(*options::err(), options::err.set(outStream));
}

#undef __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM

inline std::string checkReplayFilename(std::string option, std::string optarg, SmtEngine* smt) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay"));
  } else {
    return optarg;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

inline std::ostream* checkReplayLogFilename(std::string option, std::string optarg, SmtEngine* smt) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay-log"));
  } else if(optarg == "-") {
    return &std::cout;
  } else {
    errno = 0;
    std::ostream* replayLog = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(replayLog == NULL || !*replayLog) {
      std::stringstream ss;
      ss << "Cannot open replay-log file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
    return replayLog;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

// ensure we are a stats-enabled build of CVC4
inline void statsEnabledBuild(std::string option, bool value, SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_STATISTICS_ON
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a statistics-enabled build of CVC4; this binary was not built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_STATISTICS_ON */
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__OPTIONS_HANDLERS_H */
