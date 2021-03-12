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

IntStat::IntStat(const std::string& name, int64_t init)
    : BackedStat<int64_t>(name, init)
{
}

/** Increment the underlying integer statistic. */
IntStat& IntStat::operator++()
{
  if (CVC4_USE_STATISTICS)
  {
    ++d_data;
  }
  return *this;
}
/** Increment the underlying integer statistic. */
IntStat& IntStat::operator++(int)
{
  if (CVC4_USE_STATISTICS)
  {
    ++d_data;
  }
  return *this;
}

/** Increment the underlying integer statistic by the given amount. */
IntStat& IntStat::operator+=(int64_t val)
{
  if (CVC4_USE_STATISTICS)
  {
    d_data += val;
  }
  return *this;
}

/** Keep the maximum of the current statistic value and the given one. */
void IntStat::maxAssign(int64_t val)
{
  if (CVC4_USE_STATISTICS)
  {
    if (d_data < val)
    {
      d_data = val;
    }
  }
}

/** Keep the minimum of the current statistic value and the given one. */
void IntStat::minAssign(int64_t val)
{
  if (CVC4_USE_STATISTICS)
  {
    if (d_data > val)
    {
      d_data = val;
    }
  }
}

AverageStat::AverageStat(const std::string& name)
    : BackedStat<double>(name, 0.0)
{
}

/** Add an entry to the running-average calculation. */
AverageStat& AverageStat::operator<<(double e)
{
  if (CVC4_USE_STATISTICS)
  {
    ++d_count;
    d_sum += e;
    set(d_sum / d_count);
  }
  return *this;
}

SExpr AverageStat::getValue() const
{
  std::stringstream ss;
  ss << std::fixed << std::setprecision(8) << d_data;
  return SExpr(Rational::fromDecimal(ss.str()));
}

}  // namespace CVC4
