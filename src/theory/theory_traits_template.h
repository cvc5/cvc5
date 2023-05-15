/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A template for the theory_traits.h header, defining various
 * (static) aspects of theories
 *
 * This file is a template for the theory_traits.h header, defining
 * various (static) aspects of theories, combined with the theory
 * kinds files to produce the final header.
 */

#include "cvc5_private.h"

#pragma once

#include "options/theory_options.h"
#include "theory/theory.h"

// clang-format off
${theory_includes}
// clang-format on

namespace cvc5::internal {
namespace theory {

template <TheoryId theoryId>
struct TheoryTraits;

// clang-format off
${theory_traits}
// clang-format on

struct TheoryConstructor
{
  static void addTheory(TheoryEngine* engine, TheoryId id)
  {
    switch (id)
    {
      // clang-format off
${theory_constructors}
        // clang-format on

      default: Unhandled() << id;
    }
  }
}; /* struct cvc5::internal::theory::TheoryConstructor */

}  // namespace theory
}  // namespace cvc5::internal
