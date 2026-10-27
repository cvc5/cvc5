/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Singleton CoCoA global manager
 */

#ifdef CVC5_USE_COCOA

#include "util/cocoa_globals.h"

#include <CoCoA/GlobalManager.H>

#include <mutex>

namespace cvc5::internal {

CoCoA::GlobalManager* s_cocoaGlobalManager = nullptr;

void initCocoaGlobalManager()
{
  // CoCoA allows a single GlobalManager per process and throws if a second
  // one is constructed. Solvers may be created concurrently in different
  // threads, so the initialization must be synchronized.
  static std::once_flag s_initialized;
  std::call_once(s_initialized,
                 []() { s_cocoaGlobalManager = new CoCoA::GlobalManager(); });
}

}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
