/*********************                                                        */
/*! \file dump.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Dump utility classes and functions
 **
 ** Dump utility classes and functions.
 **/

#include "smt/dump.h"

#include "base/output.h"
#include "lib/strtok_r.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "smt/command.h"
#include "smt/node_command.h"

namespace CVC4 {

#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)

CVC4dumpstream& CVC4dumpstream::operator<<(const Command& c)
{
  if (d_os != nullptr)
  {
    (*d_os) << c;
  }
  return *this;
}

CVC4dumpstream& CVC4dumpstream::operator<<(const NodeCommand& nc)
{
  if (d_os != nullptr)
  {
    (*d_os) << nc;
  }
  return *this;
}

#else

CVC4dumpstream& CVC4dumpstream::operator<<(const Command& c) { return *this; }
CVC4dumpstream& CVC4dumpstream::operator<<(const NodeCommand& nc)
{
  return *this;
}

#endif /* CVC4_DUMPING && !CVC4_MUZZLE */

DumpC DumpChannel CVC4_PUBLIC;

std::ostream& DumpC::setStream(std::ostream* os) {
  ::CVC4::DumpOutChannel.setStream(os);
  return *os;
}
std::ostream& DumpC::getStream() { return ::CVC4::DumpOutChannel.getStream(); }
std::ostream* DumpC::getStreamPointer() { return ::CVC4::DumpOutChannel.getStreamPointer(); }


void DumpC::setDumpFromString(const std::string& optarg) {
  if (Configuration::isDumpingBuild())
  {
    // Make a copy of optarg for strtok_r to use.
    std::string optargCopy = optarg;
    char* optargPtr = const_cast<char*>(optargCopy.c_str());
    char* tokstr = optargPtr;
    char* toksave;
    while ((optargPtr = strtok_r(tokstr, ",", &toksave)) != NULL)
    {
      tokstr = NULL;
      if (!strcmp(optargPtr, "raw-benchmark"))
      {
      }
      else if (!strcmp(optargPtr, "benchmark"))
      {
      }
      else if (!strcmp(optargPtr, "declarations"))
      {
      }
      else if (!strcmp(optargPtr, "assertions"))
      {
        Dump.on("assertions:post-everything");
      }
      else if (!strncmp(optargPtr, "assertions:", 11))
      {
        const char* p = optargPtr + 11;
        if (!strncmp(p, "pre-", 4))
        {
          p += 4;
        }
        else if (!strncmp(p, "post-", 5))
        {
          p += 5;
        }
        else
        {
          throw OptionException(std::string("don't know how to dump `")
                                + optargPtr
                                + "'.  Please consult --dump help.");
        }
        if (!strcmp(p, "everything"))
        {
        }
        else if (preprocessing::PreprocessingPassRegistry::getInstance()
                     .hasPass(p))
        {
        }
        else
        {
          throw OptionException(std::string("don't know how to dump `")
                                + optargPtr
                                + "'.  Please consult --dump help.");
        }
        Dump.on("assertions");
      }
      else if (!strcmp(optargPtr, "skolems"))
      {
      }
      else if (!strcmp(optargPtr, "clauses"))
      {
      }
      else if (!strcmp(optargPtr, "t-conflicts")
               || !strcmp(optargPtr, "t-lemmas")
               || !strcmp(optargPtr, "t-explanations")
               || !strcmp(optargPtr, "bv-rewrites")
               || !strcmp(optargPtr, "theory::fullcheck"))
      {
      }
      else if (!strcmp(optargPtr, "help"))
      {
        puts(s_dumpHelp.c_str());

        std::stringstream ss;
        ss << "Available preprocessing passes:\n";
        for (const std::string& pass :
             preprocessing::PreprocessingPassRegistry::getInstance()
                 .getAvailablePasses())
        {
          ss << "- " << pass << "\n";
        }
        puts(ss.str().c_str());
        exit(1);
      }
      else
      {
        throw OptionException(std::string("unknown option for --dump: `")
                              + optargPtr + "'.  Try --dump help.");
      }

      Dump.on(optargPtr);
      Dump.on("benchmark");
      if (strcmp(optargPtr, "benchmark"))
      {
        Dump.on("declarations");
        if (strcmp(optargPtr, "declarations")
            && strcmp(optargPtr, "raw-benchmark"))
        {
          Dump.on("skolems");
        }
      }
    }
  }
  else
  {
    throw OptionException(
        "The dumping feature was disabled in this build of CVC4.");
  }
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
  boolean-terms constrain-subtypes substitution bv-to-bool bool-to-bv\n\
  strings-pp skolem-quant simplify static-learning ite-removal\n\
  repeat-simplify rewrite-apply-to-const theory-preprocessing.\n\
  PASS can also be the special value \"everything\", in which case the\n\
  assertions are printed before any preprocessing (with\n\
  \"assertions:pre-everything\") or after all preprocessing completes\n\
  (with \"assertions:post-everything\").\n\
\n\
clauses\n\
+ Do all the preprocessing outlined above, and dump the CNF-converted\n\
  output\n\
\n\
t-conflicts\n\
+ Output correctness queries for all theory conflicts\n\
\n\
t-lemmas\n\
+ Output correctness queries for all theory lemmas\n\
\n\
t-explanations\n\
+ Output correctness queries for all theory explanations\n\
\n\
bv-rewrites\n\
+ Output correctness queries for all bitvector rewrites\n\
\n\
theory::fullcheck\n\
+ Output completeness queries for all full-check effort-level theory checks\n\
\n\
Dump modes can be combined with multiple uses of --dump.  Generally you want\n\
raw-benchmark or, alternatively, one from the assertions category (either\n\
assertions or clauses), and perhaps one or more other modes\n\
for checking correctness and completeness of decision procedure implementations.\n\
\n\
The --output-language option controls the language used for dumping, and\n\
this allows you to connect CVC4 to another solver implementation via a UNIX\n\
pipe to perform on-line checking.  The --dump-to option can be used to dump\n\
to a file.\n\
";

}/* CVC4 namespace */
