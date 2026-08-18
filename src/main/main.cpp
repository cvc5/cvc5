/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Main driver for cvc5 executable.
 */
#include "main/main.h"

#include <cvc5/cvc5.h>

#include <iostream>

#include "base/configuration.h"
#include "main/command_executor.h"
#include "options/option_exception.h"
#ifdef CVC5_USE_COCOA
#include <CoCoA/error.H>
#endif

#ifdef __EMSCRIPTEN__
#include <cstring>
#include <cstdint>

/**
 * Override Emscripten's `__syscall_getrusage` stub, which corrupts memory.
 *
 * musl's getrusage() assumes `sizeof(struct timeval) == 2 * sizeof(long)` and
 * so hands the syscall a pointer deliberately biased backwards:
 *
 *   char* dest = (char*)&ru->ru_maxrss - 4 * sizeof(long);
 *
 * It expects the kernel to fill a legacy layout there (four longs holding
 * utime/stime, then the 14 remaining fields), and afterwards widens those
 * four longs back into `ru`. But wasm32 forces a 64-bit `time_t`, making
 * `struct timeval` 16 bytes rather than 8, so `&ru->ru_maxrss` is at offset
 * 32 while `4 * sizeof(long)` is only 16: `dest` lands 16 bytes *inside* the
 * caller's object instead of at its start.
 *
 * Emscripten's stub is not a kernel and does not know about that bias -- it
 * casts `dest` straight to `struct rusage*` and memsets `sizeof(struct
 * rusage)` (144) bytes from there, overrunning the real object by 16 bytes.
 * That silently clobbers whatever follows: for a stack-local `struct rusage`
 * (Minisat::cpuTime) it smashes the frame, and for a file-scope static
 * (CoCoA::CpuTime) it smashes the next object in the data segment -- in
 * practice CoCoA::GlobalManager::ourGlobalDataPtr, which then reads back as
 * null and makes CoCoALib throw ERR::NoGlobalMgr in the middle of a solve.
 *
 * The stub is declared `weak`, so this strong definition replaces it. Write
 * only the 18 longs musl actually expects at `dest`, all of which fall inside
 * the caller's buffer. Values mirror the upstream stub's fakes; Emscripten
 * has no real resource accounting to report.
 */
extern "C" int __syscall_getrusage(int who, intptr_t usage)
{
  (void)who;  // resource type ignored: this stub never does real accounting
  long* kru = reinterpret_cast<long*>(usage);
  std::memset(kru, 0, 18 * sizeof(long));
  kru[0] = 1;  // ru_utime.tv_sec
  kru[1] = 2;  // ru_utime.tv_usec
  kru[2] = 3;  // ru_stime.tv_sec
  kru[3] = 4;  // ru_stime.tv_usec
  return 0;
}
#endif

using namespace cvc5::internal;
using namespace cvc5::main;

/**
 * cvc5's main() routine is just an exception-safe wrapper around runCvc5.
 */
int main(int argc, char* argv[])
{
  cvc5::TermManager tm;
  std::unique_ptr<cvc5::Solver> solver = std::make_unique<cvc5::Solver>(tm);
  try
  {
    return runCvc5(argc, argv, solver);
  }
  catch (cvc5::CVC5ApiOptionException& e)
  {
#ifdef CVC5_COMPETITION_MODE
    solver->getDriverOptions().out() << "unknown" << std::endl;
#endif
    std::cerr << "(error \"" << e.getMessage() << "\")" << std::endl
              << std::endl
              << "Please use --help to get help on command-line options."
              << std::endl;
  }
  catch (OptionException& e)
  {
#ifdef CVC5_COMPETITION_MODE
    solver->getDriverOptions().out() << "unknown" << std::endl;
#endif
    std::cerr << "(error \"" << e.getMessage() << "\")" << std::endl
              << std::endl
              << "Please use --help to get help on command-line options."
              << std::endl;
  }
  catch (cvc5::CVC5ApiException& e)
  {
#ifdef CVC5_COMPETITION_MODE
    solver->getDriverOptions().out() << "unknown" << std::endl;
#endif
    if (solver->getOption("output-language") == "LANG_SMTLIB_V2_6")
    {
      solver->getDriverOptions().out()
          << "(error \"" << e << "\")" << std::endl;
    }
    else
    {
      solver->getDriverOptions().err()
          << "(error \"" << e << "\")" << std::endl;
    }
    if (solver->getOptionInfo("stats").boolValue() && pExecutor != nullptr)
    {
      pExecutor->printStatistics(solver->getDriverOptions().err());
    }
  }
#ifdef CVC5_USE_COCOA
  catch (CoCoA::ErrorInfo& e)
  {
    e.myOutputSelf(std::cerr);
  }
#endif
  // Make sure that the command executor is destroyed before the node manager.
  pExecutor.reset();
  exit(1);
}
