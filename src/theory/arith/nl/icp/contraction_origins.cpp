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
 * Implements a way to track the origins of ICP-style contractions.
 */

#include "theory/arith/nl/icp/contraction_origins.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

void ContractionOriginManager::getOrigins(ContractionOrigin const* const origin,
                                          std::set<Node>& res) const
{
  if (!origin->candidate.isNull())
  {
    res.insert(origin->candidate);
  }
  for (const auto& co : origin->origins)
  {
    getOrigins(co, res);
  }
}

const std::map<Node, ContractionOriginManager::ContractionOrigin*>&
ContractionOriginManager::currentOrigins() const
{
  return d_currentOrigins;
}

void ContractionOriginManager::add(const Node& targetVariable,
                                   const Node& candidate,
                                   const std::vector<Node>& originVariables,
                                   bool addTarget)
{
  Trace("nl-icp") << "Adding contraction for " << targetVariable << std::endl;
  std::vector<ContractionOrigin*> origins;
  if (addTarget)
  {
    auto it = d_currentOrigins.find(targetVariable);
    if (it != d_currentOrigins.end())
    {
      origins.emplace_back(it->second);
    }
  }
  for (const auto& v : originVariables)
  {
    auto it = d_currentOrigins.find(v);
    if (it != d_currentOrigins.end())
    {
      origins.emplace_back(it->second);
    }
  }
  d_allocations.emplace_back(
      new ContractionOrigin{candidate, std::move(origins)});
  d_currentOrigins[targetVariable] = d_allocations.back().get();
}

std::vector<Node> ContractionOriginManager::getOrigins(
    const Node& variable) const
{
  Trace("nl-icp") << "Obtaining origins for " << variable << std::endl;
  std::set<Node> origins;
  Assert(d_currentOrigins.find(variable) != d_currentOrigins.end())
      << "Using variable as origin that is unknown yet.";
  getOrigins(d_currentOrigins.at(variable), origins);
  Assert(!origins.empty()) << "There should be at least one origin";
  return std::vector<Node>(origins.begin(), origins.end());
}

bool ContractionOriginManager::isInOrigins(const Node& variable,
                                           const Node& c) const
{
  std::set<Node> origins;
  Assert(d_currentOrigins.find(variable) != d_currentOrigins.end())
      << "Using variable as origin that is unknown yet.";
  getOrigins(d_currentOrigins.at(variable), origins);
  return origins.find(c) != origins.end();
}

void print(std::ostream& os,
           const std::string& indent,
           const ContractionOriginManager::ContractionOrigin* co)
{
  os << indent << co->candidate << std::endl;
  for (const auto& o : co->origins)
  {
    print(os, indent + "\t", o);
  }
}

inline std::ostream& operator<<(std::ostream& os,
                                const ContractionOriginManager& com)
{
  os << "ContractionOrigins:" << std::endl;
  const auto& origins = com.currentOrigins();
  for (const auto& vars : origins)
  {
    os << vars.first << ":" << std::endl;
    print(os, "\t", vars.second);
  }
  return os;
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
