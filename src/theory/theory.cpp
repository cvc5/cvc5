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
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/instantiator_default.h"

#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::s_uninterpretedSortOwner = THEORY_UF;

/** By default, we use the type based theoryOf */
TheoryOfMode Theory::s_theoryOfMode = THEORY_OF_TYPE_BASED;

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::EFFORT_STANDARD:
    os << "EFFORT_STANDARD"; break;
  case Theory::EFFORT_FULL:
    os << "EFFORT_FULL"; break;
  case Theory::EFFORT_COMBINATION:
    os << "EFFORT_COMBINATION"; break;
  case Theory::EFFORT_LAST_CALL:
    os << "EFFORT_LAST_CALL"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */

Theory::~Theory() {
  if(d_inst != NULL) {
    delete d_inst;
    d_inst = NULL;
  }

  StatisticsRegistry::unregisterStat(&d_computeCareGraphTime);
}

TheoryId Theory::theoryOf(TheoryOfMode mode, TNode node) {

  Trace("theory::internal") << "theoryOf(" << node << ")" << std::endl;

  switch(mode) {
  case THEORY_OF_TYPE_BASED:
    // Constants, variables, 0-ary constructors
    if (node.isVar() || node.isConst()) {
      return theoryOf(node.getType());
    }
    // Equality is owned by the theory that owns the domain
    if (node.getKind() == kind::EQUAL) {
      return theoryOf(node[0].getType());
    }
    // Regular nodes are owned by the kind
    return kindToTheoryId(node.getKind());
    break;
  case THEORY_OF_TERM_BASED:
    // Variables
    if (node.isVar()) {
      if (theoryOf(node.getType()) != theory::THEORY_BOOL) {
        // We treat the varibables as uninterpreted
        return s_uninterpretedSortOwner;
      } else {
        // Except for the Boolean ones, which we just ignore anyhow
        return theory::THEORY_BOOL;
      }
    }
    // Constants
    if (node.isConst()) {
      // Constants go to the theory of the type
      return theoryOf(node.getType());
    }
    // Equality
    if (node.getKind() == kind::EQUAL) {
      // If one of them is an ITE, it's irelevant, since they will get replaced out anyhow
      if (node[0].getKind() == kind::ITE) {
        return theoryOf(node[0].getType());
      }
      if (node[1].getKind() == kind::ITE) {
        return theoryOf(node[1].getType());
      }
      // If both sides belong to the same theory the choice is easy
      TheoryId T1 = theoryOf(node[0]);
      TheoryId T2 = theoryOf(node[1]);
      if (T1 == T2) {
        return T1;
      }
      TheoryId T3 = theoryOf(node[0].getType());
      // This is a case of
      // * x*y = f(z) -> UF
      // * x = c      -> UF
      // * f(x) = read(a, y) -> either UF or ARRAY
      // at least one of the theories has to be parametric, i.e. theory of the type is different
      // from the theory of the term
      if (T1 == T3) {
        return T2;
      }
      if (T2 == T3) {
        return T1;
      }
      // If both are parametric, we take the smaller one (arbitraty)
      return T1 < T2 ? T1 : T2;
    }
    // Regular nodes are owned by the kind
    return kindToTheoryId(node.getKind());
    break;
  default:
    Unreachable();
  }
}

void Theory::addSharedTermInternal(TNode n) {
  Debug("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << endl;
  Debug("theory::assertions") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << endl;
  d_sharedTerms.push_back(n);
  addSharedTerm(n);
}

void Theory::computeCareGraph() {
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
  	// If we know about it, we should have propagated it, so we can skip
  	break;
      default:
  	// Let's split on it
  	addCarePair(a, b);
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

void Theory::debugPrintFacts() const{
  DebugChannel.getStream() << "Theory::debugPrintFacts()" << endl;
  printFacts(DebugChannel.getStream());
}

Instantiator::Instantiator(context::Context* c, QuantifiersEngine* qe, Theory* th) :
  d_quantEngine(qe),
  d_th(th) {
}

Instantiator::~Instantiator() {
}

void Instantiator::resetInstantiationRound(Theory::Effort effort) {
  for(int i = 0; i < (int) d_instStrategies.size(); ++i) {
    if(isActiveStrategy(d_instStrategies[i])) {
      d_instStrategies[i]->resetInstantiationRound(effort);
    }
  }
  processResetInstantiationRound(effort);
}

int Instantiator::doInstantiation(Node f, Theory::Effort effort, int e ) {
  if(hasConstraintsFrom(f)) {
    int status = process(f, effort, e );
    if(d_instStrategies.empty()) {
      Debug("inst-engine-inst") << "There are no instantiation strategies allocated." << endl;
    } else {
      for(int i = 0; i < (int) d_instStrategies.size(); ++i) {
        if(isActiveStrategy(d_instStrategies[i])) {
          Debug("inst-engine-inst") << d_instStrategies[i]->identify() << " process " << effort << endl;
          //call the instantiation strategy's process method
          int s_status = d_instStrategies[i]->doInstantiation( f, effort, e );
          Debug("inst-engine-inst") << "  -> status is " << s_status << endl;
          InstStrategy::updateStatus(status, s_status);
        } else {
          Debug("inst-engine-inst") << d_instStrategies[i]->identify() << " is not active." << endl;
        }
      }
    }
    return status;
  } else {
    Debug("inst-engine-inst") << "We have no constraints from this quantifier." << endl;
    return InstStrategy::STATUS_SAT;
  }
}

//void Instantiator::doInstantiation(int effort) {
//  d_status = InstStrategy::STATUS_SAT;
//  for( int q = 0; q < d_quantEngine->getNumQuantifiers(); ++q ) {
//    Node f = d_quantEngine->getQuantifier(q);
//    if( d_quantEngine->getActive(f) && hasConstraintsFrom(f) ) {
//      int d_quantStatus = process( f, effort );
//      InstStrategy::updateStatus( d_status, d_quantStatus );
//      for( int i = 0; i < (int)d_instStrategies.size(); ++i ) {
//        if( isActiveStrategy( d_instStrategies[i] ) ) {
//          Debug("inst-engine-inst") << d_instStrategies[i]->identify() << " process " << effort << endl;
//          //call the instantiation strategy's process method
//          d_quantStatus = d_instStrategies[i]->process( f, effort );
//          Debug("inst-engine-inst") << "  -> status is " << d_quantStatus << endl;
//          InstStrategy::updateStatus( d_status, d_quantStatus );
//        }
//      }
//    }
//  }
//}

void Instantiator::setHasConstraintsFrom(Node f) {
  d_hasConstraints[f] = true;
  if(! d_quantEngine->hasOwner(f)) {
    d_quantEngine->setOwner(f, getTheory());
  } else if(d_quantEngine->getOwner(f) != getTheory()) {
    d_quantEngine->setOwner(f, NULL);
  }
}

bool Instantiator::hasConstraintsFrom(Node f) {
  return d_hasConstraints.find(f) != d_hasConstraints.end() && d_hasConstraints[f];
}

bool Instantiator::isOwnerOf(Node f) {
  return d_quantEngine->hasOwner(f) && d_quantEngine->getOwner(f) == getTheory();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
