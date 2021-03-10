/*********************                                                        */
/*! \file stats_base.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base statistic classes
 **
 ** Base statistic classes
 **/

#include "util/stats_base.h"

#include "util/statistics_registry.h"

namespace CVC4 {

Stat::Stat(const std::string& name) : d_name(name)
{
  if (CVC4_USE_STATISTICS)
  {
    CheckArgument(d_name.find(", ") == std::string::npos,
                  name,
                  "Statistics names cannot include a comma (',')");
  }
}

}  // namespace CVC4
