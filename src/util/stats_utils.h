/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistic utilities.
 */

#include "cvc4_private_library.h"

#ifndef CVC5__UTIL__STATS_UTILS_H
#define CVC5__UTIL__STATS_UTILS_H

#include <iosfwd>

#include "cvc4_export.h"

namespace cvc5 {

namespace timer_stat_detail {
struct duration;
}

std::ostream& operator<<(std::ostream& os,
                         const timer_stat_detail::duration& dur) CVC4_EXPORT;

}  // namespace cvc5

#endif
