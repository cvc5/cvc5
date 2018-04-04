/*********************                                                        */
/*! \file sygus_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif
 **/

#include "theory/quantifiers/sygus/sygus_unif.h"

#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusUnif::SygusUnif() :
d_qe(nullptr),
d_tds(nullptr),
d_check_sol(false),
d_cond_count(0)
{
}

SygusUnif::~SygusUnif() {}

void SygusUnif::initialize(QuantifiersEngine* qe,
                           Node f,
                           std::vector<Node>& enums,
                           std::vector<Node>& lemmas)
{
  Assert(d_candidate.isNull());
  d_candidate = f;
  d_qe = qe;
  d_tds = qe->getTermDatabaseSygus();
  // initialize the strategy
  d_strategy.initialize(qe, f, enums, lemmas);
}

Node SygusUnif::constructSolution()
{
  Node c = d_candidate;
  if (!d_solution.isNull())
  {
    // already has a solution
    return d_solution;
  }
  // only check if an enumerator updated
  if (d_check_sol)
  {
    Trace("sygus-pbe") << "Construct solution, #iterations = " << d_cond_count
                       << std::endl;
    d_check_sol = false;
    // try multiple times if we have done multiple conditions, due to
    // non-determinism
    Node vc;
    for (unsigned i = 0; i <= d_cond_count; i++)
    {
      Trace("sygus-pbe-dt") << "ConstructPBE for candidate: " << c << std::endl;
      Node e = d_strategy.getRootEnumerator();
      // initialize a call to construct solution
      initializeConstructSol();
      // call the virtual construct solution method
      Node vcc = constructSol(e, role_equal, 1);
      // if we constructed the solution, and we either did not previously have
      // a solution, or the new solution is better (smaller).
      if (!vcc.isNull()
          && (vc.isNull() || (!vc.isNull()
                              && d_tds->getSygusTermSize(vcc)
                                     < d_tds->getSygusTermSize(vc))))
      {
        Trace("sygus-pbe") << "**** SygusUnif SOLVED : " << c << " = " << vcc
                           << std::endl;
        Trace("sygus-pbe") << "...solved at iteration " << i << std::endl;
        vc = vcc;
      }
    }
    if (!vc.isNull())
    {
      d_solution = vc;
      return vc;
    }
    Trace("sygus-pbe") << "...failed to solve." << std::endl;
  }
  return Node::null();
}

Node SygusUnif::constructBestSolvedTerm(const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestStringSolvedTerm(const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestSolvedConditional(const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestConditional(const std::vector<Node>& conds)
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
    const std::map<Node, unsigned>& total_inc,
    const std::map<Node, std::vector<unsigned> >& incr)
{
  Assert(!strs.empty());
  std::vector<Node> strs_tmp = strs;
  std::random_shuffle(strs_tmp.begin(), strs_tmp.end());
  // prefer one that has incremented by more than 0
  for (const Node& ns : strs_tmp)
  {
    const std::map<Node, unsigned>::const_iterator iti = total_inc.find(ns);
    if (iti != total_inc.end() && iti->second > 0)
    {
      return ns;
    }
  }
  return strs_tmp[0];
}

void SygusUnif::indent(const char* c, int ind)
{
  if (Trace.isOn(c))
  {
    for (int i = 0; i < ind; i++)
    {
      Trace(c) << "  ";
    }
  }
}

void SygusUnif::print_val(const char* c, std::vector<Node>& vals, bool pol)
{
  if (Trace.isOn(c))
  {
    for (unsigned i = 0; i < vals.size(); i++)
    {
      Trace(c) << ((pol ? vals[i].getConst<bool>() : !vals[i].getConst<bool>())
                       ? "1"
                       : "0");
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
