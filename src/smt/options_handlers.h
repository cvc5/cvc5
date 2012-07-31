/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

#include "util/dump.h"

namespace CVC4 {
namespace smt {

static const std::string dumpHelp = "\
Dump modes currently supported by the --dump option:\n\
\n\
benchmark\n\
+ Dump the benchmark structure (set-logic, push/pop, queries, etc.), but\n\
  does not include any declarations or assertions.  Implied by all following\n\
  modes.\n\
\n\
declarations\n\
+ Dump declarations.  Implied by all following modes.\n\
\n\
assertions\n\
+ Output the assertions after non-clausal simplification and static\n\
  learning phases, but before presolve-time T-lemmas arrive.  If\n\
  non-clausal simplification and static learning are off\n\
  (--simplification=none --no-static-learning), the output\n\
  will closely resemble the input (with term-level ITEs removed).\n\
\n\
learned\n\
+ Output the assertions after non-clausal simplification, static\n\
  learning, and presolve-time T-lemmas.  This should include all eager\n\
  T-lemmas (in the form provided by the theory, which my or may not be\n\
  clausal).  Also includes level-0 BCP done by Minisat.\n\
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
one from the assertions category (either assertions, learned, or clauses), and\n\
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
    } else if(!strcmp(optargPtr, "learned")) {
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
    }
  }
  free(optargPtr);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline void dumpToFile(std::string option, std::string optarg, SmtEngine* smt) {
#ifdef CVC4_DUMPING
  size_t dagSetting = expr::ExprDag::getDag(Dump.getStream());
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --dump-to"));
  } else if(optarg == "-") {
    Dump.setStream(DumpOutC::dump_cout);
  } else {
    std::ostream* dumpTo = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(!*dumpTo) {
      throw OptionException(std::string("Cannot open dump-to file (maybe it exists): `") + optarg + "'");
    }
    Dump.setStream(*dumpTo);
  }
  expr::ExprDag::setDag(Dump.getStream(), dagSetting);
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
    std::ostream* replayLog = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(!*replayLog) {
      throw OptionException(std::string("Cannot open replay-log file: `") + optarg + "'");
    }
    return replayLog;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__OPTIONS_HANDLERS_H */
