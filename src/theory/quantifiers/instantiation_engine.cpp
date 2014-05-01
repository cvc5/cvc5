/*********************                                                        */
/*! \file instantiation_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

InstantiationEngine::InstantiationEngine( QuantifiersEngine* qe, bool setIncomplete ) :
QuantifiersModule( qe ), d_isup(NULL), d_i_ag(NULL), d_setIncomplete( setIncomplete ), d_ierCounter( 0 ), d_performCheck( false ){

}

InstantiationEngine::~InstantiationEngine() {
  delete d_i_ag;
  delete d_isup;
}

void InstantiationEngine::finishInit(){
  //for UF terms
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    //if( options::cbqi() ){
    //  addInstStrategy( new InstStrategyCheckCESolved( this, d_quantEngine ) );
    //}
    //these are the instantiation strategies for basic E-matching
    if( options::userPatternsQuant()!=USER_PAT_MODE_IGNORE ){
      d_isup = new InstStrategyUserPatterns( d_quantEngine );
      addInstStrategy( d_isup );
    }else{
      d_isup = NULL;
    }
    d_i_ag = new InstStrategyAutoGenTriggers( d_quantEngine, Trigger::TS_ALL, 3 );
    d_i_ag->setGenerateAdditional( true );
    addInstStrategy( d_i_ag );
    //addInstStrategy( new InstStrategyAddFailSplits( this, ie ) );
    if( !options::finiteModelFind() && options::fullSaturateQuant() ){
      addInstStrategy( new InstStrategyFreeVariable( d_quantEngine ) );
    }
    //d_isup->setPriorityOver( d_i_ag );
    //d_isup->setPriorityOver( i_agm );
    //i_ag->setPriorityOver( i_agm );
  }
  //for arithmetic
  if( options::cbqi() ){
    addInstStrategy( new InstStrategySimplex( (arith::TheoryArith*)d_quantEngine->getTheoryEngine()->theoryOf( THEORY_ARITH ), d_quantEngine ) );
  }
  //for datatypes
  //if( options::cbqi() ){
  //  addInstStrategy( new InstStrategyDatatypesValue( d_quantEngine ) );
  //}
}


bool InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  //if counterexample-based quantifier instantiation is active
  if( options::cbqi() ){
    //check if any cbqi lemma has not been added yet
    bool addedLemma = false;
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( doCbqi( f ) && !hasAddedCbqiLemma( f ) ){
        d_added_cbqi_lemma[f] = true;
        Debug("cbqi") << "Do cbqi for " << f << std::endl;
        //add cbqi lemma
        //get the counterexample literal
        Node ceLit = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
        if( !ceLit.isNull() ){
          //require any decision on cel to be phase=true
          d_quantEngine->getOutputChannel().requirePhase( ceLit, true );
          Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
          //add counterexample lemma
          NodeBuilder<> nb(kind::OR);
          nb << f << ceLit;
          Node lem = nb;
          Trace("cbqi") << "Counterexample lemma : " << lem << std::endl;
          d_quantEngine->getOutputChannel().lemma( lem, false, true );
          addedLemma = true;
        }
      }
    }
    if( addedLemma ){
      return true;
    }
  }
  //if not, proceed to instantiation round
  Debug("inst-engine") << "IE: Instantiation Round." << std::endl;
  Debug("inst-engine-ctrl") << "IE: Instantiation Round." << std::endl;
  //reset the quantifiers engine
  Debug("inst-engine-ctrl") << "Reset IE" << std::endl;
  //reset the instantiators
  for( size_t i=0; i<d_instStrategies.size(); ++i ){
    InstStrategy* is = d_instStrategies[i];
    if( isActiveStrategy( is ) ){
      is->processResetInstantiationRound( effort );
    }
  }
  //iterate over an internal effort level e
  int e = 0;
  int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
  d_inst_round_status = InstStrategy::STATUS_UNFINISHED;
  //while unfinished, try effort level=0,1,2....
  while( d_inst_round_status==InstStrategy::STATUS_UNFINISHED && e<=eLimit ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    d_inst_round_status = InstStrategy::STATUS_SAT;
    //instantiate each quantifier
    for( int q=0; q<d_quantEngine->getModel()->getNumAssertedQuantifiers(); q++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( q );
      Debug("inst-engine-debug") << "IE: Instantiate " << f << "..." << std::endl;
      //if this quantifier is active
      if( d_quant_active[ f ] ){
        //int e_use = d_quantEngine->getRelevance( f )==-1 ? e - 1 : e;
        int e_use = e;
        if( e_use>=0 ){
          //check each instantiation strategy
          for( size_t i=0; i<d_instStrategies.size(); ++i ){
            InstStrategy* is = d_instStrategies[i];
            if( isActiveStrategy( is ) && is->shouldProcess( f ) ){
              Debug("inst-engine-debug") << "Do " << is->identify() << " " << e_use << std::endl;
              int quantStatus = is->process( f, effort, e_use );
              Debug("inst-engine-debug") << " -> status is " << quantStatus << std::endl;
              InstStrategy::updateStatus( d_inst_round_status, quantStatus );
            }
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if( d_quantEngine->hasAddedLemma() ){
      d_inst_round_status = InstStrategy::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "All instantiators finished, # added lemmas = ";
  Debug("inst-engine") << (int)d_quantEngine->d_lemmas_waiting.size() << std::endl;
  //Notice() << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( !d_quantEngine->hasAddedLemma() ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state." << std::endl;
    Debug("inst-engine-ctrl") << "---Fail." << std::endl;
    return false;
  }else{
    Debug("inst-engine-ctrl") << "---Done. " << (int)d_quantEngine->d_lemmas_waiting.size() << std::endl;
    Trace("inst-engine") << "Added lemmas = " << (int)d_quantEngine->d_lemmas_waiting.size() << std::endl;
    //flush lemmas to output channel
    d_quantEngine->flushLemmas( &d_quantEngine->getOutputChannel() );
    return true;
  }
}

bool InstantiationEngine::needsCheck( Theory::Effort e ){
  if( e==Theory::EFFORT_FULL ){
    d_ierCounter++;
  }
  //determine if we should perform check, based on instWhenMode
  d_performCheck = false;
  if( options::instWhenMode()==INST_WHEN_FULL ){
    d_performCheck = ( e >= Theory::EFFORT_FULL );
  }else if( options::instWhenMode()==INST_WHEN_FULL_DELAY ){
    d_performCheck = ( e >= Theory::EFFORT_FULL ) && !d_quantEngine->getTheoryEngine()->needCheck();
  }else if( options::instWhenMode()==INST_WHEN_FULL_LAST_CALL ){
    d_performCheck = ( ( e==Theory::EFFORT_FULL  && d_ierCounter%2==0 ) || e==Theory::EFFORT_LAST_CALL );
  }else if( options::instWhenMode()==INST_WHEN_LAST_CALL ){
    d_performCheck = ( e >= Theory::EFFORT_LAST_CALL );
  }else{
    d_performCheck = true;
  }
  static int ierCounter2 = 0;
  if( e==Theory::EFFORT_LAST_CALL ){
    ierCounter2++;
    //with bounded integers, skip every other last call,
    // since matching loops may occur with infinite quantification
    if( ierCounter2%2==0 && options::fmfBoundInt() ){
      d_performCheck = false;
    }
  }

  return d_performCheck;
}

void InstantiationEngine::check( Theory::Effort e ){
  if( d_performCheck && !d_quantEngine->hasAddedLemma() ){
    Debug("inst-engine") << "IE: Check " << e << " " << d_ierCounter << std::endl;
    double clSet = 0;
    if( Trace.isOn("inst-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "---Instantiation Engine Round, effort = " << e << "---" << std::endl;
    }
    ++(d_statistics.d_instantiation_rounds);
    bool quantActive = false;
    Debug("quantifiers") << "quantifiers:  check:  asserted quantifiers size"
                         << d_quantEngine->getModel()->getNumAssertedQuantifiers() << std::endl;
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node n = d_quantEngine->getModel()->getAssertedQuantifier( i );
      //it is not active if we have found the skolemized negation is unsat
      if( TermDb::isRewriteRule( n ) ){
        d_quant_active[n] = false;
      }else if( options::cbqi() && hasAddedCbqiLemma( n ) ){
        Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( n );
        bool active, value;
        bool ceValue = false;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          active = value;
          ceValue = true;
        }else{
          active = true;
        }
        d_quant_active[n] = active;
        if( active ){
          Debug("quantifiers") << "  Active : " << n;
          if( !TermDb::hasInstConstAttr(n) ){
            quantActive = true;
          }
        }else{
          Debug("quantifiers") << "  NOT active : " << n;
          if( d_quantEngine->getValuation().isDecision( cel ) ){
            Debug("quant-req-phase") << "Bad decision : " << cel << std::endl;
          }
          //note that the counterexample literal must not be a decision
          Assert( !d_quantEngine->getValuation().isDecision( cel ) );
        }
        if( d_quantEngine->getValuation().hasSatValue( n, value ) ){
          Debug("quantifiers") << ", value = " << value;
        }
        if( ceValue ){
          Debug("quantifiers") << ", ce is asserted";
        }
        Debug("quantifiers") << std::endl;
      //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
      }else{
        d_quant_active[n] = true;
        if( !TermDb::hasInstConstAttr(n) ){
          quantActive = true;
        }
        Debug("quantifiers") << "  Active : " << n << ", no ce assigned." << std::endl;
      }
      Debug("quantifiers-relevance")  << "Quantifier : " << n << std::endl;
      if( options::relevantTriggers() ){
        Debug("quantifiers-relevance")  << "   Relevance : " << d_quantEngine->getQuantifierRelevance()->getRelevance( n ) << std::endl;
        Debug("quantifiers") << "   Relevance : " << d_quantEngine->getQuantifierRelevance()->getRelevance( n ) << std::endl;
      }
      Trace("inst-engine-debug") << "Process : " << n << " " << d_quant_active[n] << std::endl;
    }
    if( quantActive ){
      bool addedLemmas = doInstantiationRound( e );
      //Debug("quantifiers-dec") << "Do instantiation, level = " << d_quantEngine->getValuation().getDecisionLevel() << std::endl;
      //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      //  Debug("quantifiers-dec") << "   " << d_valuation.getDecision( i ) << std::endl;
      //}
      if( e==Theory::EFFORT_LAST_CALL ){
        if( !addedLemmas ){
          if( d_inst_round_status==InstStrategy::STATUS_SAT ){
            Debug("inst-engine") << "No instantiation given, returning SAT..." << std::endl;
            debugSat( SAT_INST_STRATEGY );
          }else if( d_setIncomplete ){
            Debug("inst-engine") << "No instantiation given, returning unknown..." << std::endl;
            d_quantEngine->getOutputChannel().setIncomplete();
          }else{
            Assert( options::finiteModelFind() );
            Debug("inst-engine") << "No instantiation given, defer to another engine..." << std::endl;
          }
        }
      }
    }else{
      if( e==Theory::EFFORT_LAST_CALL ){
        if( options::cbqi() ){
          debugSat( SAT_CBQI );
        }
      }
    }
    if( Trace.isOn("inst-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "Finished instantiation engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

void InstantiationEngine::registerQuantifier( Node f ){
  if( !TermDb::isRewriteRule( f ) ){
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
        addUserPattern( f, subsPat[i] );
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
  if( options::cbqi.wasSetByUser() ){
    return options::cbqi();
  }else if( options::cbqi() ){
    //if quantifier has a non-arithmetic variable, then do not use cbqi
    //if quantifier has an APPLY_UF term, then do not use cbqi
    return !hasNonArithmeticVariable( f ) && !hasApplyUf( f[1] );
  }else{
    return false;
  }
}














void InstantiationEngine::debugSat( int reason ){
  if( reason==SAT_CBQI ){
    //Debug("quantifiers-sat") << "Decisions:" << std::endl;
    //for( int i=1; i<=(int)d_quantEngine->getValuation().getDecisionLevel(); i++ ){
    //  Debug("quantifiers-sat") << "   " << i << ": " << d_quantEngine->getValuation().getDecision( i ) << std::endl;
    //}
    //for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
    //  if( (*i).second ) {
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
      Assert( !cel.isNull() );
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
        if( !value ){
          AlwaysAssert(! d_quantEngine->getValuation().isDecision( cel ),
                       "bad decision on counterexample literal");
        }
      }
    }
    //}
    Debug("quantifiers-sat") << "return SAT: Cbqi, no quantifier is active. " << std::endl;
    //static bool setTrust = false;
    //if( !setTrust ){
    //  setTrust = true;
    //  Notice() << "trust-";
    //}
  }else if( reason==SAT_INST_STRATEGY ){
    Debug("quantifiers-sat") << "return SAT: No strategy chose to add an instantiation." << std::endl;
    //Notice() << "sat ";
    //Unimplemented();
  }
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
          //if not already set, propagate as decision
          Debug("cbqi-prop-as-dec") << "CBQI: propagate as decision " << cel << std::endl;
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

InstantiationEngine::Statistics::Statistics():
  d_instantiations_user_patterns("InstantiationEngine::Instantiations_User_Patterns", 0),
  d_instantiations_auto_gen("InstantiationEngine::Instantiations_Auto_Gen", 0),
  d_instantiations_auto_gen_min("InstantiationEngine::Instantiations_Auto_Gen_Min", 0),
  d_instantiations_guess("InstantiationEngine::Instantiations_Guess", 0),
  d_instantiations_cbqi_arith("InstantiationEngine::Instantiations_Cbqi_Arith", 0),
  d_instantiations_cbqi_arith_minus("InstantiationEngine::Instantiations_Cbqi_Arith_Minus", 0),
  d_instantiations_cbqi_datatypes("InstantiationEngine::Instantiations_Cbqi_Datatypes", 0),
  d_instantiation_rounds("InstantiationEngine::Rounds", 0 )
{
  StatisticsRegistry::registerStat(&d_instantiations_user_patterns);
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen);
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen_min);
  StatisticsRegistry::registerStat(&d_instantiations_guess);
  StatisticsRegistry::registerStat(&d_instantiations_cbqi_arith);
  StatisticsRegistry::registerStat(&d_instantiations_cbqi_arith_minus);
  StatisticsRegistry::registerStat(&d_instantiations_cbqi_datatypes);
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
}

InstantiationEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations_user_patterns);
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen);
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen_min);
  StatisticsRegistry::unregisterStat(&d_instantiations_guess);
  StatisticsRegistry::unregisterStat(&d_instantiations_cbqi_arith);
  StatisticsRegistry::unregisterStat(&d_instantiations_cbqi_arith_minus);
  StatisticsRegistry::unregisterStat(&d_instantiations_cbqi_datatypes);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
}
