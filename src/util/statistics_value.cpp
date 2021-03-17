/*********************                                                        */
/*! \file statistics_value.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistic data classes
 **
 ** The statistic data classes that actually hold the data for the statistics.
 **
 ** Conceptually, every statistic consists of a data object and a proxy object.
 ** The data objects (statistic values) are derived from `StatisticBaseValue`
 ** and live in the `StatisticRegistry`.
 ** They are solely exported to the proxy objects, which should be the sole
 ** way to manipulate the data of a data object.
 ** The data objects themselves need to implement printing (normal and safe) and
 ** conversion to the API type `Stat`.
 **/

#include "util/statistics_value.h"

#include "util/ostream_util.h"

namespace CVC4 {

void StatisticTimerValue::print(std::ostream& out) const
  {
    StreamFormatScope format_scope(out);
    duration dur = get();

    out << (dur / std::chrono::seconds(1)) << "." << std::setfill('0')
        << std::setw(9) << std::right
        << (dur % std::chrono::seconds(1)).count();
  }

}  // namespace CVC4
