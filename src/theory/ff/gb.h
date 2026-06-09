/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finding common zeros using Groebner bases.
 */

#ifdef CVC5_USE_COCOA

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__GB_H
#define CVC5__THEORY__FF__GB_H

// std includes
#include <vector>

// internal includes
#include "smt/env.h"
#include "theory/ff/stats.h"
#include "theory/ff/util.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** Find a model for these facts using one GB call and model construction.
 *
 * @param facts Finite field equalities and disequalities.
 * @param size The size of the field they are in.
 * @param env used for resource management
 * @param stats FfStatistics to track
 *
 * @return A model or a conflict core.
 * */
FfResult gb(const std::vector<Node>& facts,
            const FfSize& size,
            const Env& env,
            FfStatistics* stats = nullptr);

}
}
}

#endif  // CVC5__THEORY__FF__GB_H

#endif
