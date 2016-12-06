/*********************                                                        */
/*! \file dump.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Dump utility classes and functions
 **
 ** Dump utility classes and functions.
 **/

#include "smt/dump.h"
#include "lib/strtok_r.h"
#include "base/output.h"

namespace CVC4 {

DumpC DumpChannel CVC4_PUBLIC;

std::ostream& DumpC::setStream(std::ostream* os) {
  ::CVC4::DumpOutChannel.setStream(os);
  return *os;
}
std::ostream& DumpC::getStream() { return ::CVC4::DumpOutChannel.getStream(); }
std::ostream* DumpC::getStreamPointer() { return ::CVC4::DumpOutChannel.getStreamPointer(); }


void DumpC::setDumpFromString(const std::string& optarg) {
#ifdef CVC4_DUMPING
  // Make a copy of optarg for strtok_r to use.
  std::string optargCopy = optarg;
  char* optargPtr = const_cast<char*>(optargCopy.c_str());
  char* tokstr = optargPtr;
  char* toksave;
  while((optargPtr = strtok_r(tokstr, ",", &toksave)) != NULL) {
    tokstr = NULL;
    if(!strcmp(optargPtr, "raw-benchmark")) {
    } else if(!strcmp(optargPtr, "benchmark")) {
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
      } else if(!strcmp(p, "strings-pp")) {
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
      puts(s_dumpHelp.c_str());
      exit(1);
    } else if(!strcmp(optargPtr, "bv-abstraction")) {
      Dump.on("bv-abstraction");
    } else if(!strcmp(optargPtr, "bv-algebraic")) {
      Dump.on("bv-algebraic");
    } else {
      throw OptionException(std::string("unknown option for --dump: `") +
                            optargPtr + "'.  Try --dump help.");
    }

    Dump.on(optargPtr);
    Dump.on("benchmark");
    if(strcmp(optargPtr, "benchmark")) {
      Dump.on("declarations");
      if(strcmp(optargPtr, "declarations") && strcmp(optargPtr, "raw-benchmark")) {
        Dump.on("skolems");
      }
    }
  }
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}


const std::string DumpC::s_dumpHelp = "\
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
raw-benchmark\n\
+ Dump all user-commands as they are received (including assertions) without\n\
  any preprocessing and without any internally-created commands.\n\
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
  boolean-terms constrain-subtypes substitution strings-pp skolem-quant\n\
  simplify static-learning ite-removal repeat-simplify\n\
  rewrite-apply-to-const theory-preprocessing.\n\
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
bv-abstraction [non-stateful]\n\
+ Output correctness queries for all bv abstraction \n\
\n\
bv-algebraic [non-stateful]\n\
+ Output correctness queries for bv algebraic solver. \n\
\n\
theory::fullcheck [non-stateful]\n\
+ Output completeness queries for all full-check effort-level theory checks\n\
\n\
Dump modes can be combined with multiple uses of --dump.  Generally you want\n\
raw-benchmark or, alternatively, one from the assertions category (either\n\
assertions or clauses), and perhaps one or more stateful or non-stateful modes\n\
for checking correctness and completeness of decision procedure implementations.\n\
Stateful modes dump the contextual assertions made by the core solver (all\n\
decisions and propagations as assertions); this affects the validity of the\n\
resulting correctness and completeness queries, so of course stateful and\n\
non-stateful modes cannot be mixed in the same run.\n\
\n\
The --output-language option controls the language used for dumping, and\n\
this allows you to connect CVC4 to another solver implementation via a UNIX\n\
pipe to perform on-line checking.  The --dump-to option can be used to dump\n\
to a file.\n\
";

}/* CVC4 namespace */
