/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility methods.
 */

#ifndef CVC5__UTILS_H
#define CVC5__UTILS_H

#include <cvc5/cvc5.h>

namespace utils {

/**
 * Print solutions for synthesis conjecture to the standard output stream.
 * @param terms the terms for which the synthesis solutions were retrieved
 * @param sols the synthesis solutions of the given terms
 */
void printSynthSolutions(const std::vector<cvc5::Term>& terms,
                         const std::vector<cvc5::Term>& sols);

}  // namespace utils

#endif  // CVC5__UTILS_H
