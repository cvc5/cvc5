/*********************                                                        */
/*! \file statistics_viewer.cpp
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

#include "util/statistics_viewer.h"

#include <iostream>

// standard helper, see https://en.cppreference.com/w/cpp/utility/variant/visit
template <class... Ts>
struct overloaded : Ts...
{
  using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

namespace CVC4 {

bool StatViewer::isInt() const
{
  return std::holds_alternative<int64_t>(d_data);
}
int64_t StatViewer::getInt() const
{
  assert(isInt());
  return std::get<int64_t>(d_data);
}
bool StatViewer::isDouble() const
{
  return std::holds_alternative<double>(d_data);
}
double StatViewer::getDouble() const
{
  assert(isDouble());
  return std::get<double>(d_data);
}
bool StatViewer::isString() const
{
  return std::holds_alternative<std::string>(d_data);
}
std::string StatViewer::getString() const
{
  assert(isString());
  return std::get<std::string>(d_data);
}
bool StatViewer::isHistogram() const
{
  return std::holds_alternative<HistogramData>(d_data);
}
const StatViewer::HistogramData& StatViewer::getHistogram() const
{
  assert(isHistogram());
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

}  // namespace CVC4
