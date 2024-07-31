/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility methods.
 */

#ifndef CVC5__C_UTILS_H
#define CVC5__C_UTILS_H

#include <cvc5/c/cvc5.h>

/**
 * Print solutions for synthesis conjecture to the stdout.
 * @param nterms The number of terms.
 * @param terms  The terms for which the synthesis solutions were retrieved.
 * @param sols   The synthesis solutions of the given terms.
 */
void print_synth_solutions(size_t nterms,
                           const Cvc5Term terms[],
                           const Cvc5Term sols[]);

#endif
