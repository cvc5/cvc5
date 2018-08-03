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
}

QueryGenerator::QueryGenerator() : d_sampler(nullptr) {}

void QueryGenerator::initialize(SygusSampler* ss) { d_sampler = ss; }

void QueryGenerator::addTerm(Node n)
{
  Trace("sygus-qg") << "QueryGenerator::addTerm : " << n << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
