/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Registration and documentation for all public statistics.
 */

#include "cvc5_private_library.h"

#ifndef CVC5__UTIL__STATISTICS_PUBLIC_H
#define CVC5__UTIL__STATISTICS_PUBLIC_H

namespace cvc5::internal {

class StatisticsRegistry;

/**
 * Preregisters all public statistics.
 */
void registerPublicStatistics(StatisticsRegistry& reg);

}  // namespace cvc5::internal

#endif
