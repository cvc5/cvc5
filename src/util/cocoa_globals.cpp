/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

CoCoA::GlobalManager* s_cocoaGlobalManager = nullptr;

void initCocoaGlobalManager()
{
  if (s_cocoaGlobalManager == nullptr)
  {
    s_cocoaGlobalManager = new CoCoA::GlobalManager();
  }
}

}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
