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
 * Singleton CoCoA global manager.
 *
 * A manager must be created before most CoCoA operations are performed.
 *
 * It must be created **exactly once** (per process, we believe). Creating it
 * multiple times raises an exception.
 *
 * It is never directly used by our code: no component of our code accesses it.
 *
 * Thus, we store it on a heap, with a static pointer to it. It is thus shared
 * across the entire process (and in particular, all cvc5 solvers).
 */

#include "cvc5_public.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__UTIL__COCOA_GLOBALS_H
#define CVC5__UTIL__COCOA_GLOBALS_H

#include <CoCoA/GlobalManager.H>

namespace cvc5::internal {

/**
 * The pointer to the singleton CoCoA global manager.
 */
extern CoCoA::GlobalManager* s_cocoaGlobalManager;

/**
 * Intializes the CoCoA global manager if it has not been intialized already.
 */
void initCocoaGlobalManager();

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__COCOA_GLOBALS_H */

#endif /* CVC5_USE_COCOA */
