/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_unif.
 */

#include "theory/quantifiers/sygus/sygus_unif.h"

#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "util/random.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusUnif::SygusUnif(Env& env)
    : EnvObj(env), d_tds(nullptr), d_enableMinimality(false)
{
}

SygusUnif::~SygusUnif() {}

void SygusUnif::initializeCandidate(
    TermDbSygus* tds,
    Node f,
    std::vector<Node>& enums,
    std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  d_tds = tds;
  d_candidates.push_back(f);
  // initialize the strategy
  d_strategy.emplace(f, SygusUnifStrategy(d_env));
  d_strategy.at(f).initialize(tds, f, enums);
}

Node SygusUnif::getMinimalTerm(const std::vector<Node>& terms)
{
  unsigned minSize = 0;
  Node minTerm;
  std::map<Node, unsigned>::iterator it;
  for (const Node& n : terms)
  {
    it = d_termToSize.find(n);
    unsigned ssize = 0;
    if (it == d_termToSize.end())
    {
      ssize = datatypes::utils::getSygusTermSize(n);
      d_termToSize[n] = ssize;
    }
    else
    {
      ssize = it->second;
    }
    if (minTerm.isNull() || ssize < minSize)
    {
      minTerm = n;
      minSize = ssize;
    }
  }
  return minTerm;
}

Node SygusUnif::constructBestSolvedTerm(Node e, const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  if (d_enableMinimality)
  {
    return getMinimalTerm(solved);
  }
  return solved[0];
}

Node SygusUnif::constructBestConditional(Node ce,
                                         const std::vector<Node>& conds)
{
  Assert(!conds.empty());
  double r = Random::getRandom().pickDouble(0.0, 1.0);
  unsigned cindex = r * conds.size();
  if (cindex > conds.size())
  {
    cindex = conds.size() - 1;
  }
  return conds[cindex];
}

Node SygusUnif::constructBestStringToConcat(
    const std::vector<Node>& strs,
    const std::map<Node, size_t>& total_inc,
    const std::map<Node, std::vector<size_t>>& incr)
{
  Assert(!strs.empty());
  std::vector<Node> strs_tmp = strs;
  std::shuffle(strs_tmp.begin(), strs_tmp.end(), Random::getRandom());
  // prefer one that has incremented by more than 0
  for (const Node& ns : strs_tmp)
  {
    const std::map<Node, size_t>::const_iterator iti = total_inc.find(ns);
    if (iti != total_inc.end() && iti->second > 0)
    {
      return ns;
    }
  }
  return strs_tmp[0];
}

void SygusUnif::indent(const char* c, int ind)
{
  if (TraceIsOn(c))
  {
    for (int i = 0; i < ind; i++)
    {
      Trace(c) << "  ";
    }
  }
}

void SygusUnif::print_val(const char* c, std::vector<Node>& vals, bool pol)
{
  if (TraceIsOn(c))
  {
    for (unsigned i = 0; i < vals.size(); i++)
    {
      Trace(c) << ((pol ? vals[i].getConst<bool>() : !vals[i].getConst<bool>())
                       ? "1"
                       : "0");
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
