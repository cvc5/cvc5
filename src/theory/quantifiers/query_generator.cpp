/*********************                                                        */
/*! \file query_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of query_generator
 **/

#include "theory/quantifiers/query_generator.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void QGTTrie::addTerm(Node n,
                      LazyTrieEvaluator* eval,
                      unsigned deqAllow,
                      unsigned index,
                      unsigned ntotal,
                      bool exact)
{
  if( index==ntotal )
  {
    if( exact )
    {
      d_waiting.push_back(n);
    }
    else
    {
      // we have a query
      Assert( !d_waiting.empty() );
    }
    return;
  }
  // if there are waiting nodes, expand
  if( !d_waiting.empty() )
  {
    Assert( d_children.empty() );
  }
  
}

QueryGenerator::QueryGenerator() : d_sampler(nullptr) {}

void QueryGenerator::initialize(SygusSampler* ss, unsigned deqThresh) { d_sampler = ss; d_deq_thresh = deqThresh; }

void QueryGenerator::addTerm(Node n)
{
  Trace("sygus-qg") << "QueryGenerator::addTerm : " << n << std::endl;
  unsigned npts = d_sampler->getNumSamplePoints();
  TypeNode tn = n.getType();
  //d_qgt_trie[tn].addTerm(n,d_sampler,d_deq_thresh,0,npts);
  d_qgt_trie[tn].add(n, d_sampler, 0, npts, false);
  
  // get the appropriate lazy trie for the sampler
  
  
  
  
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
