/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

class StatisticsRegistry;

/**
 * Preregisters all public (non-expert) statistics.
 */
void registerPublicStatistics(StatisticsRegistry& reg);

}  // namespace cvc5

#endif
