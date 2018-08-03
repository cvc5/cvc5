/*********************                                                        */
/*! \file expr_miner.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expr_miner
 **/

#include "theory/quantifiers/expr_miner.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
ExpressionMiner::ExpressionMiner()
{
  
}

void ExpressionMiner::initialize(ExtendedRewriter* er,
                TypeNode tn,
                std::vector<Node>& vars,
                unsigned nsamples,
                bool unique_type_ids)
{
  d_crd.initialize(&d_sampler, er, tn, vars, nsamples, unique_type_ids);
}

void ExpressionMiner::initializeSygus(QuantifiersEngine* qe,
                      Node f,
                      unsigned nsamples,
                      bool useSygusType)
{
  d_crd.initializeSygus(&d_sampler, qe, f, nsamples, useSygusType);
  
}

bool ExpressionMiner::addTerm(Node sol, std::ostream& out, bool& rew_print)
{
  bool ret = d_crd.addTerm(sol,out,rew_print);
  if( ret )
  {
    // a unique term, let's try the query generator
    d_qg.addTerm(sol);
  }
  return ret;
}

bool ExpressionMiner::addTerm(Node sol, std::ostream& out)
{
  bool rew_print = false;
  return addTerm(sol,out,rew_print);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
