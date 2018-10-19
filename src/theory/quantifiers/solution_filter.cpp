/*********************                                                        */
/*! \file solution_filter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for filtering solutions.
 **/

#include "theory/quantifiers/solution_filter.h"

#include <fstream>
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SolutionFilter::SolutionFilter() {}

void SolutionFilter::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  ExprMiner::initialize(vars, ss);
}

bool SolutionFilter::addTerm(Node n, std::ostream& out)
{
  if( n.isConst() )
  {
    if( n.getConst<bool>() )
    {
      return false;
    }
    else
    {
      // could abort after printing here
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  Node imp = d_conj.isNull() ? n.negate() : nm->mkNode(AND, d_conj, n.negate());
  Trace("sygus-cf-implied") << "  implies: check " << imp << "..." << std::endl;
  // make the satisfiability query
  bool needExport = false;
  ExprManagerMapCollection varMap;
  ExprManager em(nm->getOptions());
  std::unique_ptr<SmtEngine> queryChecker;
  initializeChecker(queryChecker, em, varMap, imp, needExport);
  Result r = queryChecker->checkSat();
  Trace("sygus-cf-implied") << "  implies: ...got : " << r << std::endl;
  if( r.asSatisfiabilityResult().isSat() != Result::UNSAT )
  {
    d_conj = d_conj.isNull() ? n : nm->mkNode( AND, d_conj, n );
    return true;
  }
  Trace("sygus-cf-implied-filter") << "Filtered : " << n << std::endl;
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
