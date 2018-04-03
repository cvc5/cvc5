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

SygusUnif::SygusUnif()
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
    // try multiple times if we have done multiple conditions, due to non-determinism
    Node vc;
    for (unsigned i = 0; i <= d_cond_count; i++)
    {
      Trace("sygus-pbe-dt")
          << "ConstructPBE for candidate: " << c << std::endl;
      Node e = d_strategy.getRootEnumerator();
      // initialize a call to construct solution
      initializeConstructSol();
      // call the virtual construct solution method
      Node vcc = constructSol(e, role_equal, 1);
      if (!vcc.isNull())
      {
        if (vc.isNull() || (!vc.isNull()
                            && d_tds->getSygusTermSize(vcc)
                                    < d_tds->getSygusTermSize(vc)))
        {
          Trace("sygus-pbe") << "**** SygusUnif SOLVED : " << c << " = " << vcc << std::endl;
          Trace("sygus-pbe") << "...solved at iteration " << i << std::endl;
          vc = vcc;
        }
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

Node SygusUnif::constructBestSolvedTerm(std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestStringSolvedTerm(std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestSolvedConditional(std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestConditional(std::vector<Node>& conds)
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
    std::vector<Node> strs,
    std::map<Node, unsigned> total_inc,
    std::map<Node, std::vector<unsigned> > incr)
{
  Assert(!strs.empty());
  std::random_shuffle(strs.begin(), strs.end());
  // prefer one that has incremented by more than 0
  for (const Node& ns : strs)
  {
    if (total_inc[ns] > 0)
    {
      return ns;
    }
  }
  return strs[0];
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
