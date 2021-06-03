/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Macros which run code when the old or new proof system is enabled,
 * or unsat cores are enabled.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__PROOF_MACROS_H
#define CVC5__THEORY__ARITH__PROOF_MACROS_H

#include "options/smt_options.h"

#define ARITH_PROOF(x)                \
  if (cvc5::options::produceProofs()) \
  {                                   \
    x;                                \
  }
#define ARITH_NULLPROOF(x) (cvc5::options::produceProofs()) ? x : NULL
#define ARITH_PROOF_ON() cvc5::options::produceProofs()

#endif  // CVC5__THEORY__ARITH__PROOF_MACROS_H
