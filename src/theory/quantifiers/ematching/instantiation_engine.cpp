/*********************                                                        */
/*! \file instantiation_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiation engine class
 **/

#include "theory/quantifiers/ematching/instantiation_engine.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/inst_strategy_e_matching.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;

InstantiationEngine::InstantiationEngine(QuantifiersEngine* qe)
    : QuantifiersModule(qe),
      d_instStrategies(),
      d_isup(),
      d_i_ag(),
      d_quants(),
      d_quant_rel(nullptr)
{
  if (options::relevantTriggers())
  {
    d_quant_rel.reset(new quantifiers::QuantRelevance);
  }
  if (options::eMatching()) {
    // these are the instantiation strategies for E-matching
    // user-provided patterns
    if (options::userPatternsQuant() != options::UserPatMode::IGNORE)
    {
      d_isup.reset(new InstStrategyUserPatterns(d_quantEngine));
      d_instStrategies.push_back(d_isup.get());
    }

    // auto-generated patterns
    d_i_ag.reset(
        new InstStrategyAutoGenTriggers(d_quantEngine, d_quant_rel.get()));
    d_instStrategies.push_back(d_i_ag.get());
  }
}

InstantiationEngine::~InstantiationEngine() {}

void InstantiationEngine::presolve() {
  for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    d_instStrategies[i]->presolve();
  }
}

void InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  unsigned lastWaiting = d_quantEngine->getNumLemmasWaiting();
  //iterate over an internal effort level e
  int e = 0;
  int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
  bool finished = false;
  //while unfinished, try effort level=0,1,2....
  while( !finished && e<=eLimit ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    finished = true;
    //instantiate each quantifier
    for( unsigned i=0; i<d_quants.size(); i++ ){
      Node q = d_quants[i];
      Debug("inst-engine-debug") << "IE: Instantiate " << q << "..." << std::endl;
      //int e_use = d_quantEngine->getRelevance( q )==-1 ? e - 1 : e;
      int e_use = e;
      if( e_use>=0 ){
        Trace("inst-engine-debug") << "inst-engine : " << q << std::endl;
        //check each instantiation strategy
        for( unsigned j=0; j<d_instStrategies.size(); j++ ){
          InstStrategy* is = d_instStrategies[j];
          Trace("inst-engine-debug") << "Do " << is->identify() << " " << e_use << std::endl;
          int quantStatus = is->process( q, effort, e_use );
          Trace("inst-engine-debug") << " -> status is " << quantStatus << ", conflict=" << d_quantEngine->inConflict() << std::endl;
          if( d_quantEngine->inConflict() ){
            return;
          }else if( quantStatus==InstStrategy::STATUS_UNFINISHED ){
            finished = false;
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if( d_quantEngine->getNumLemmasWaiting()>lastWaiting ){
      finished = true;
    }
    e++;
  }
}

bool InstantiationEngine::needsCheck( Theory::Effort e ){
  return d_quantEngine->getInstWhenNeedsCheck( e );
}

void InstantiationEngine::reset_round( Theory::Effort e ){
  //if not, proceed to instantiation round
  //reset the instantiation strategies
  for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    InstStrategy* is = d_instStrategies[i];
    is->processResetInstantiationRound( e );
  }
}

void InstantiationEngine::check(Theory::Effort e, QEffort quant_e)
{
  CodeTimer codeTimer(d_quantEngine->d_statistics.d_ematching_time);
  if (quant_e == QEFFORT_STANDARD)
  {
    double clSet = 0;
    if( Trace.isOn("inst-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "---Instantiation Engine Round, effort = " << e << "---" << std::endl;
    }
    //collect all active quantified formulas belonging to this
    bool quantActive = false;
    d_quants.clear();
    for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node q = d_quantEngine->getModel()->getAssertedQuantifier( i, true );
      if( d_quantEngine->hasOwnership( q, this ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
        quantActive = true;
        d_quants.push_back( q );
      }
    }
    Trace("inst-engine-debug") << "InstEngine: check: # asserted quantifiers " << d_quants.size() << "/";
    Trace("inst-engine-debug") << d_quantEngine->getModel()->getNumAssertedQuantifiers() << " " << quantActive << std::endl;
    if( quantActive ){
      unsigned lastWaiting = d_quantEngine->getNumLemmasWaiting();
      doInstantiationRound( e );
      if( d_quantEngine->inConflict() ){
        Assert(d_quantEngine->getNumLemmasWaiting() > lastWaiting);
        Trace("inst-engine") << "Conflict, added lemmas = " << (d_quantEngine->getNumLemmasWaiting()-lastWaiting) << std::endl;
      }else if( d_quantEngine->hasAddedLemma() ){
        Trace("inst-engine") << "Added lemmas = " << (d_quantEngine->getNumLemmasWaiting()-lastWaiting)  << std::endl;
      }
    }else{
      d_quants.clear();
    }
    if( Trace.isOn("inst-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "Finished instantiation engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool InstantiationEngine::checkCompleteFor( Node q ) {
  //TODO?
  return false;
}

void InstantiationEngine::checkOwnership(Node q)
{
  if( options::strictTriggers() && q.getNumChildren()==3 ){
    //if strict triggers, take ownership of this quantified formula
    bool hasPat = false;
    for( unsigned i=0; i<q[2].getNumChildren(); i++ ){
      if( q[2][i].getKind()==INST_PATTERN || q[2][i].getKind()==INST_NO_PATTERN  ){
        hasPat = true;
        break;
      }
    }
    if( hasPat ){
      d_quantEngine->setOwner( q, this, 1 );
    }
  }
}

void InstantiationEngine::registerQuantifier(Node q)
{
  if (!d_quantEngine->hasOwnership(q, this))
  {
    return;
  }
  if (d_quant_rel)
  {
    d_quant_rel->registerQuantifier(q);
  }
  // take into account user patterns
  if (q.getNumChildren() == 3)
  {
    Node subsPat =
        d_quantEngine->getTermUtil()->substituteBoundVariablesToInstConstants(
            q[2], q);
    // add patterns
    for (const Node& p : subsPat)
    {
      if (p.getKind() == INST_PATTERN)
      {
        addUserPattern(q, p);
      }
      else if (p.getKind() == INST_NO_PATTERN)
      {
        addUserNoPattern(q, p);
      }
    }
  }
}

void InstantiationEngine::addUserPattern(Node q, Node pat) {
  if (d_isup) {
    d_isup->addUserPattern(q, pat);
  }
}

void InstantiationEngine::addUserNoPattern(Node q, Node pat) {
  if (d_i_ag) {
    d_i_ag->addUserNoPattern(q, pat);
  }
}
