/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base for theory interface.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"
#include "util/Assert.h"

#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::s_uninterpretedSortOwner = THEORY_UF;

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::MIN_EFFORT:
    os << "MIN_EFFORT"; break;
  case Theory::QUICK_CHECK:
    os << "QUICK_CHECK"; break;
  case Theory::STANDARD:
    os << "STANDARD"; break;
  case Theory::FULL_EFFORT:
    os << "FULL_EFFORT"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */

void Theory::addSharedTermInternal(TNode n) {
  Debug("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << std::endl;
  d_sharedTerms.push_back(n);
  addSharedTerm(n);
}

void Theory::computeCareGraph(CareGraph& careGraph) {
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << std::endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
  	// If we know about it, we should have propagated it, so we can skip
  	break;
      default:
  	// Let's split on it
  	careGraph.push_back(CarePair(a, b, getId()));
  	break;
      }
    }  
  }
}

void Theory::printFacts(std::ostream& os) const {
  unsigned i, n = d_facts.size();
  for(i = 0; i < n; i++){
    const Assertion& a_i = d_facts[i];
    Node assertion  = a_i;
    os << d_id << '[' << i << ']' << " " << assertion << endl;
  }
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
