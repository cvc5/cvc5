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
 * Statistic utilities.
 */

#include "util/stats_utils.h"

#include <chrono>
#include <iomanip>
#include <iostream>

#include "util/ostream_util.h"
#include "util/stats_timer.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& os,
                         const timer_stat_detail::duration& dur)
{
  StreamFormatScope format_scope(os);

  return os << (dur / std::chrono::seconds(1)) << "." << std::setfill('0')
            << std::setw(9) << std::right
            << (dur % std::chrono::seconds(1)).count();
}

}  // namespace cvc5
