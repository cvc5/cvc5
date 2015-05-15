/*********************                                                        */
/*! \file instantiation_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of instantiation engine class
 **/

#include "theory/quantifiers/instantiation_engine.h"

#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/inst_strategy_e_matching.h"
#include "theory/quantifiers/inst_strategy_cbqi.h"
#include "theory/quantifiers/trigger.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;

InstantiationEngine::InstantiationEngine( QuantifiersEngine* qe ) :
QuantifiersModule( qe ), d_isup(NULL), d_i_ag(NULL), d_i_lte(NULL), d_i_fs(NULL), d_i_splx(NULL), d_i_cegqi( NULL ){

}

InstantiationEngine::~InstantiationEngine() {
  delete d_i_ag;
  delete d_isup;
  delete d_i_lte;
  delete d_i_fs;
  delete d_i_splx;
  delete d_i_cegqi;
}

void InstantiationEngine::finishInit(){
  if( options::eMatching() ){
    //these are the instantiation strategies for E-matching

    //user-provided patterns
    if( options::userPatternsQuant()!=USER_PAT_MODE_IGNORE ){
      d_isup = new InstStrategyUserPatterns( d_quantEngine );
      d_instStrategies.push_back( d_isup );
    }

    //auto-generated patterns
    d_i_ag = new InstStrategyAutoGenTriggers( d_quantEngine );
    d_instStrategies.push_back( d_i_ag );
  }

  //local theory extensions TODO?
  //if( options::localTheoryExt() ){
  //  d_i_lte = new InstStrategyLocalTheoryExt( d_quantEngine );
  //  d_instStrategies.push_back( d_i_lte );
  //}

  //full saturation : instantiate from relevant domain, then arbitrary terms
  if( options::fullSaturateQuant() ){
    d_i_fs = new InstStrategyFreeVariable( d_quantEngine );
    d_instStrategies.push_back( d_i_fs );
  }

  //counterexample-based quantifier instantiation
  if( options::cbqi() ){
    if( !options::cbqi2() || options::cbqi.wasSetByUser() ){
      d_i_splx = new InstStrategySimplex( (arith::TheoryArith*)d_quantEngine->getTheoryEngine()->theoryOf( THEORY_ARITH ), d_quantEngine );
      d_instStrategies.push_back( d_i_splx );
    }
    if( options::cbqi2() ){
      d_i_cegqi = new InstStrategyCegqi( d_quantEngine );
      d_instStrategies.push_back( d_i_cegqi );
    }
  }
}


bool InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  unsigned lastWaiting = d_quantEngine->d_lemmas_waiting.size();
  //if counterexample-based quantifier instantiation is active
  if( options::cbqi() ){
    //check if any cbqi lemma has not been added yet
    bool addedLemma = false;
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( doCbqi( f ) && !hasAddedCbqiLemma( f ) ){
        d_added_cbqi_lemma[f] = true;
        Trace("cbqi") << "Do cbqi for " << f << std::endl;
        //add cbqi lemma
        //get the counterexample literal
        Node ceLit = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
        Node ceBody = d_quantEngine->getTermDatabase()->getInstConstantBody( f );
        if( !ceBody.isNull() ){
          //add counterexample lemma
          Node lem = NodeManager::currentNM()->mkNode( OR, ceLit.negate(), ceBody.negate() );
          //require any decision on cel to be phase=true
          d_quantEngine->addRequirePhase( ceLit, true );
          Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
          //add counterexample lemma
          lem = Rewriter::rewrite( lem );
          Trace("cbqi") << "Counterexample lemma : " << lem << std::endl;
          d_quantEngine->addLemma( lem, false );
          addedLemma = true;
        }
      }
    }
    if( addedLemma ){
      return true;
    }
  }
  //if not, proceed to instantiation round
  //reset the instantiation strategies
  for( size_t i=0; i<d_instStrategies.size(); ++i ){
    InstStrategy* is = d_instStrategies[i];
    is->processResetInstantiationRound( effort );
  }

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
        for( size_t i=0; i<d_instStrategies.size(); ++i ){
          InstStrategy* is = d_instStrategies[i];
          Trace("inst-engine-debug") << "Do " << is->identify() << " " << e_use << std::endl;
          int quantStatus = is->process( q, effort, e_use );
          Trace("inst-engine-debug") << " -> status is " << quantStatus << std::endl;
          if( quantStatus==InstStrategy::STATUS_UNFINISHED ){
            finished = false;
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if( d_quantEngine->d_lemmas_waiting.size()>lastWaiting ){
      finished = true;
    }
    e++;
  }
  //Notice() << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( !d_quantEngine->hasAddedLemma() ){
    return false;
  }else{
    Trace("inst-engine") << "Added lemmas = " << (int)(d_quantEngine->d_lemmas_waiting.size()-lastWaiting)  << std::endl;
    return true;
  }
}

bool InstantiationEngine::needsCheck( Theory::Effort e ){
  return d_quantEngine->getInstWhenNeedsCheck( e );
}

void InstantiationEngine::reset_round( Theory::Effort e ) {
  if( options::cbqi() ){
    //set inactive the quantified formulas whose CE literals are asserted false
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
      if( d_quantEngine->hasOwnership( q, this ) && d_quantEngine->getModel()->isQuantifierActive( q ) && hasAddedCbqiLemma( q ) ){
        Debug("cbqi-debug") << "Check quantified formula " << q << "..." << std::endl;
        Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( q );
        bool value;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          Debug("cbqi-debug") << "...CE Literal has value " << value << std::endl;
          if( !value ){
            d_quantEngine->getModel()->setQuantifierActive( q, false );
            if( d_quantEngine->getValuation().isDecision( cel ) ){
              Trace("cbqi-warn") << "CBQI WARNING: Bad decision on CE Literal." << std::endl;
            }
          }
        }else{
          Debug("cbqi-debug") << "...CE Literal does not have value " << std::endl;
        }
      }
    }
  }
}

void InstantiationEngine::check( Theory::Effort e, unsigned quant_e ){
  if( quant_e==QuantifiersEngine::QEFFORT_STANDARD ){
    double clSet = 0;
    if( Trace.isOn("inst-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "---Instantiation Engine Round, effort = " << e << "---" << std::endl;
    }
    ++(d_statistics.d_instantiation_rounds);
    bool quantActive = false;
    d_quants.clear();
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node n = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( d_quantEngine->hasOwnership( n, this ) && d_quantEngine->getModel()->isQuantifierActive( n ) ){
        if( !options::cbqi() || !TermDb::hasInstConstAttr(n) ){
          quantActive = true;
        }
        d_quants.push_back( n );
      }
    }
    Trace("inst-engine-debug") << "InstEngine: check: # asserted quantifiers " << d_quants.size() << "/";
    Trace("inst-engine-debug") << d_quantEngine->getModel()->getNumAssertedQuantifiers() << " " << quantActive << std::endl;
    if( quantActive ){
      bool addedLemmas = doInstantiationRound( e );
      Trace("inst-engine-debug") << "Add lemmas = " << addedLemmas << std::endl;
    }else{
      d_quants.clear();
    }
    if( Trace.isOn("inst-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "Finished instantiation engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool InstantiationEngine::checkComplete() {
  for( unsigned i=0; i<d_quants.size(); i++ ){
    if( isIncomplete( d_quants[i] ) ){
      return false;
    }
  }
  return true;
}

void InstantiationEngine::registerQuantifier( Node f ){
  if( d_quantEngine->hasOwnership( f, this ) ){
    //Notice() << "do cbqi " << f << " ? " << std::endl;
    if( options::cbqi() ){
      Node ceBody = d_quantEngine->getTermDatabase()->getInstConstantBody( f );
      if( !doCbqi( f ) ){
        d_quantEngine->addTermToDatabase( ceBody, true );
      }
    }

    //take into account user patterns
    if( f.getNumChildren()==3 ){
      Node subsPat = d_quantEngine->getTermDatabase()->getInstConstantNode( f[2], f );
      //add patterns
      for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
        //Notice() << "Add pattern " << subsPat[i] << " for " << f << std::endl;
        if( subsPat[i].getKind()==INST_PATTERN ){
          addUserPattern( f, subsPat[i] );
        }else if( subsPat[i].getKind()==INST_NO_PATTERN ){
          addUserNoPattern( f, subsPat[i] );
        }
      }
    }
  }
}

void InstantiationEngine::assertNode( Node f ){
  ////if we are doing cbqi and have not added the lemma yet, do so
  //if( doCbqi( f ) && !hasAddedCbqiLemma( f ) ){
  //  addCbqiLemma( f );
  //}
}

bool InstantiationEngine::hasApplyUf( Node f ){
  if( f.getKind()==APPLY_UF ){
    return true;
  }else{
    for( int i=0; i<(int)f.getNumChildren(); i++ ){
      if( hasApplyUf( f[i] ) ){
        return true;
      }
    }
    return false;
  }
}
bool InstantiationEngine::hasNonArithmeticVariable( Node f ){
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    TypeNode tn = f[0][i].getType();
    if( !tn.isInteger() && !tn.isReal() ){
      return true;
    }
  }
  return false;
}

bool InstantiationEngine::doCbqi( Node f ){
  if( options::cbqi.wasSetByUser() || options::cbqi2.wasSetByUser() ){
    return options::cbqi();
  }else if( options::cbqi() ){
    //if quantifier has a non-arithmetic variable, then do not use cbqi
    //if quantifier has an APPLY_UF term, then do not use cbqi
    return !hasNonArithmeticVariable( f ) && !hasApplyUf( f[1] );
  }else{
    return false;
  }
}

bool InstantiationEngine::isIncomplete( Node f ) {
  return true;
  //TODO : ensure completeness for local theory extensions
  //if( d_i_lte ){
  //return !d_i_lte->isLocalTheoryExt( f );
}












Node InstantiationEngine::getNextDecisionRequest(){
  //propagate as decision all counterexample literals that are not asserted
  if( options::cbqi() ){
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( hasAddedCbqiLemma( f ) ){
        Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
        bool value;
        if( !d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          Debug("cbqi-prop-as-dec") << "CBQI: get next decision " << cel << std::endl;
          return cel;
        }
      }
    }
  }
  return Node::null();
}

void InstantiationEngine::addUserPattern( Node f, Node pat ){
  if( d_isup ){
    d_isup->addUserPattern( f, pat );
  }
}

void InstantiationEngine::addUserNoPattern( Node f, Node pat ){
  if( d_i_ag ){
    d_i_ag->addUserNoPattern( f, pat );
  }
}

InstantiationEngine::Statistics::Statistics():
  d_instantiations_user_patterns("InstantiationEngine::Instantiations_User_Patterns", 0),
  d_instantiations_auto_gen("InstantiationEngine::Instantiations_Auto_Gen", 0),
  d_instantiations_guess("InstantiationEngine::Instantiations_Guess", 0),
  d_instantiations_cbqi_arith("InstantiationEngine::Instantiations_Cbqi_Arith", 0),
  d_instantiations_cbqi_arith_minus("InstantiationEngine::Instantiations_Cbqi_Arith_Minus", 0),
  d_instantiations_cbqi_datatypes("InstantiationEngine::Instantiations_Cbqi_Datatypes", 0),
  d_instantiations_lte("InstantiationEngine::Instantiations_Local_T_Ext", 0),
  d_instantiation_rounds("InstantiationEngine::Rounds", 0 )
{
  StatisticsRegistry::registerStat(&d_instantiations_user_patterns);
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen);
  StatisticsRegistry::registerStat(&d_instantiations_guess);
  StatisticsRegistry::registerStat(&d_instantiations_cbqi_arith);
  StatisticsRegistry::registerStat(&d_instantiations_cbqi_arith_minus);
  StatisticsRegistry::registerStat(&d_instantiations_cbqi_datatypes);
  StatisticsRegistry::registerStat(&d_instantiations_lte);
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
}

InstantiationEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations_user_patterns);
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen);
  StatisticsRegistry::unregisterStat(&d_instantiations_guess);
  StatisticsRegistry::unregisterStat(&d_instantiations_cbqi_arith);
  StatisticsRegistry::unregisterStat(&d_instantiations_cbqi_arith_minus);
  StatisticsRegistry::unregisterStat(&d_instantiations_cbqi_datatypes);
  StatisticsRegistry::unregisterStat(&d_instantiations_lte);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
}
