/*********************                                                        */
/*! \file statistics_api.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics representation for API
 **
 ** Everything necessary to inspect and print statistics via the API.
 **/

#include "util/statistics_api.h"

#include <iostream>

#include "base/check.h"
#include "util/statistics_reg.h"
#include "util/statistics_value.h"

// standard helper, see https://en.cppreference.com/w/cpp/utility/variant/visit
template <class... Ts>
struct overloaded : Ts...
{
  using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

namespace CVC4 {

bool StatViewer::isExpert() const
{
  return d_expert;
}

bool StatViewer::isInt() const
{
  return std::holds_alternative<int64_t>(d_data);
}
int64_t StatViewer::getInt() const
{
  Assert(isInt());
  return std::get<int64_t>(d_data);
}
bool StatViewer::isDouble() const
{
  return std::holds_alternative<double>(d_data);
}
double StatViewer::getDouble() const
{
  Assert(isDouble());
  return std::get<double>(d_data);
}
bool StatViewer::isString() const
{
  return std::holds_alternative<std::string>(d_data);
}
std::string StatViewer::getString() const
{
  Assert(isString());
  return std::get<std::string>(d_data);
}
bool StatViewer::isHistogram() const
{
  return std::holds_alternative<HistogramData>(d_data);
}
const StatViewer::HistogramData& StatViewer::getHistogram() const
{
  Assert(isHistogram());
  return std::get<HistogramData>(d_data);
}

std::ostream& operator<<(std::ostream& os, const StatViewer& sv)
{
  std::visit(overloaded{
                 [&os](int64_t v) { os << v; },
                 [&os](uint64_t v) { os << v; },
                 [&os](double v) { os << v; },
                 [&os](const std::string& v) { os << v; },
                 [&os](const StatViewer::HistogramData& v) {
                   os << "{ ";
                   bool first = true;
                   for (const auto& e : v)
                   {
                     if (!first)
                       os << ", ";
                     else
                       first = false;
                     os << e.first << ": " << e.second;
                   }
                   os << " }";
                 },
             },
             sv.d_data);
  return os;
}

Statistics::BaseType::const_reference Statistics::iterator::operator*() const
{
  return d_it.operator*();
}
Statistics::BaseType::const_pointer Statistics::iterator::operator->() const
{
  return d_it.operator->();
}
Statistics::iterator& Statistics::iterator::operator++()
{
  do
  {
    ++d_it;
  } while (!isVisible());
  return *this;
}
Statistics::iterator Statistics::iterator::operator++(int)
{
  iterator tmp = *this;
  do
  {
    ++d_it;
  } while (!isVisible());
  return tmp;
}
Statistics::iterator& Statistics::iterator::operator--()
{
  do
  {
    --d_it;
  } while (!isVisible());
  return *this;
}
Statistics::iterator Statistics::iterator::operator--(int)
{
  iterator tmp = *this;
  do
  {
    --d_it;
  } while (!isVisible());
  return tmp;
}
bool Statistics::iterator::operator==(const Statistics::iterator& rhs) const
{
  return d_it == rhs.d_it;
}
bool Statistics::iterator::operator!=(const Statistics::iterator& rhs) const
{
  return d_it != rhs.d_it;
}
Statistics::iterator::iterator(Statistics::BaseType::const_iterator it,
                               const Statistics::BaseType& base,
                               bool expert)
    : d_it(it), d_base(&base), d_showExpert(expert)
{
  while (!isVisible())
  {
    ++d_it;
  }
}
bool Statistics::iterator::isVisible() const
    {
      return d_showExpert || d_it == d_base->end() || !d_it->second.isExpert();
    }

Statistics::Statistics(const StatisticRegistry& reg)
{
  for (const auto& svp : reg)
  {
    d_stats.emplace(svp.first, svp.second->getViewer());
  }
}

const StatViewer& Statistics::get(const std::string& name)
{
  auto it = d_stats.find(name);
  Assert(it != d_stats.end());
  return it->second;
}

std::ostream& operator<<(std::ostream& out, const Statistics& stats)
{
  for (const auto& stat : stats)
  {
    out << stat.first << " = " << stat.second << std::endl;
  }
  return out;
}

}  // namespace CVC4
