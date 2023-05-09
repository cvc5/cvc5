/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistic data classes
 *
 * The statistic data classes that actually hold the data for the statistics.
 *
 * Conceptually, every statistic consists of a data object and a proxy object.
 * The data objects (statistic values) are derived from `StatisticBaseValue`
 * and live in the `StatisticsRegistry`.
 * They are solely exported to the proxy objects, which should be the sole
 * way to manipulate the data of a data object.
 * The data objects themselves need to implement printing (normal and safe) and
 * conversion to the API type `Stat`.
 */

#include "util/statistics_value.h"

#include "util/ostream_util.h"

namespace cvc5::internal {

// standard helper, see https://en.cppreference.com/w/cpp/utility/variant/visit
template <class... Ts>
struct overloaded : Ts...
{
  using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

namespace detail {
std::ostream& print(std::ostream& out, const StatExportData& sed)
{
  std::visit(overloaded{
                 [&out](int64_t v) { out << v; },
                 [&out](uint64_t v) { out << v; },
                 [&out](double v) { out << v; },
                 [&out](const std::string& v) { out << v; },
                 [&out](const std::map<std::string, uint64_t>& v) {
                   out << "{ ";
                   bool first = true;
                   for (const auto& e : v)
                   {
                     if (!first)
                       out << ", ";
                     else
                       first = false;
                     out << e.first << ": " << e.second;
                   }
                   out << " }";
                 },
             },
             sed);
  return out;
}
}

StatisticBaseValue::~StatisticBaseValue() {}

std::ostream& operator<<(std::ostream& out, const StatisticBaseValue& sbv)
{
  return detail::print(out, sbv.getViewer());
}

StatExportData StatisticAverageValue::getViewer() const { return get(); }

bool StatisticAverageValue::isDefault() const { return d_count == 0; }

void StatisticAverageValue::printSafe(int fd) const
{
  safe_print<double>(fd, get());
}

double StatisticAverageValue::get() const { return d_sum / d_count; }

StatExportData StatisticTimerValue::getViewer() const
{
  return std::to_string(get()) + "ms";
}

bool StatisticTimerValue::isDefault() const
{
  return !d_running && d_duration.count() == 0;
}

void StatisticTimerValue::printSafe(int fd) const
{
  safe_print<uint64_t>(fd, get());
  safe_print<std::string>(fd, "ms");
}

/** Make sure that we include the time of a currently running timer */
uint64_t StatisticTimerValue::get() const
{
  auto data = d_duration;
  if (d_running)
  {
    data += clock::now() - d_start;
  }
  return static_cast<int64_t>(data / std::chrono::milliseconds(1));
}

}  // namespace cvc5::internal
