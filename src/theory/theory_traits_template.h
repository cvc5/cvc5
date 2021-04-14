/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Dejan Jovanovic, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include "cvc4_private.h"

#pragma once

#include "options/theory_options.h"
#include "theory/theory.h"

${theory_includes}

namespace cvc5 {
namespace theory {

template <TheoryId theoryId>
struct TheoryTraits;

${theory_traits}

struct TheoryConstructor {
  static void addTheory(TheoryEngine* engine, TheoryId id) {
    switch(id) {

${theory_constructors}

default: Unhandled() << id;
    }
  }
}; /* struct cvc5::theory::TheoryConstructor */

}  // namespace theory
}  // namespace cvc5
