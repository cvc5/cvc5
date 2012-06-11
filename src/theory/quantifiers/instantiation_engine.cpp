/*********************                                                        */
/*! \file instantiation_engine.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of instantiation engine class
 **/

#include "theory/quantifiers/instantiation_engine.h"

#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

//#define IE_PRINT_PROCESS_TIMES

InstantiationEngine::InstantiationEngine( TheoryQuantifiers* th ) :
d_th( th ){

}

QuantifiersEngine* InstantiationEngine::getQuantifiersEngine(){
  return d_th->getQuantifiersEngine();
}

bool InstantiationEngine::hasAddedCbqiLemma( Node f ) {
  return d_ce_lit.find( f ) != d_ce_lit.end();
}

void InstantiationEngine::addCbqiLemma( Node f ){
  Assert( doCbqi( f ) && !hasAddedCbqiLemma( f ) );
  //code for counterexample-based quantifier instantiation
  Debug("cbqi") << "Do cbqi for " << f << std::endl;
  //make the counterexample body
  //Node ceBody = f[1].substitute( getQuantifiersEngine()->d_vars[f].begin(), getQuantifiersEngine()->d_vars[f].end(),
  //                              getQuantifiersEngine()->d_inst_constants[f].begin(),
  //                              getQuantifiersEngine()->d_inst_constants[f].end() );
  //get the counterexample literal
  Node ceBody = getQuantifiersEngine()->getCounterexampleBody( f );
  Node ceLit = d_th->getValuation().ensureLiteral( ceBody.notNode() );
  d_ce_lit[ f ] = ceLit;
  getQuantifiersEngine()->setInstantiationConstantAttr( ceLit, f );
  // set attributes, mark all literals in the body of n as dependent on cel
  //registerLiterals( ceLit, f );
  //require any decision on cel to be phase=true
  d_th->getOutputChannel().requirePhase( ceLit, true );
  Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
  //add counterexample lemma
  NodeBuilder<> nb(kind::OR);
  nb << f << ceLit;
  Node lem = nb;
  Debug("cbqi-debug") << "Counterexample lemma : " << lem << std::endl;
  d_th->getOutputChannel().lemma( lem );
}

bool InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  //if counterexample-based quantifier instantiation is active
  if( Options::current()->cbqi ){
    //check if any cbqi lemma has not been added yet
    bool addedLemma = false;
    for( int i=0; i<(int)getQuantifiersEngine()->getNumAssertedQuantifiers(); i++ ){
      Node f = getQuantifiersEngine()->getAssertedQuantifier( i );
      if( doCbqi( f ) && !hasAddedCbqiLemma( f ) ){
        //add cbqi lemma
        addCbqiLemma( f );
        addedLemma = true;
      }
    }
    if( addedLemma ){
      return true;
    }
  }
  //if not, proceed to instantiation round
  Debug("inst-engine") << "IE: Instantiation Round." << std::endl;
  Debug("inst-engine-ctrl") << "IE: Instantiation Round." << std::endl;
  //reset instantiators
  Debug("inst-engine-ctrl") << "Reset IE" << std::endl;
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( getQuantifiersEngine()->getInstantiator( i ) ){
      getQuantifiersEngine()->getInstantiator( i )->resetInstantiationRound( effort );
    }
  }
  getQuantifiersEngine()->getTermDatabase()->reset( effort );
  //iterate over an internal effort level e
  int e = 0;
  int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
  d_inst_round_status = InstStrategy::STATUS_UNFINISHED;
  //while unfinished, try effort level=0,1,2....
  while( d_inst_round_status==InstStrategy::STATUS_UNFINISHED && e<=eLimit ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    d_inst_round_status = InstStrategy::STATUS_SAT;
    //instantiate each quantifier
    for( int q=0; q<getQuantifiersEngine()->getNumAssertedQuantifiers(); q++ ){
      Node f = getQuantifiersEngine()->getAssertedQuantifier( q );
      Debug("inst-engine-debug") << "IE: Instantiate " << f << "..." << std::endl;
      //if this quantifier is active
      if( getQuantifiersEngine()->getActive( f ) ){
        //int e_use = getQuantifiersEngine()->getRelevance( f )==-1 ? e - 1 : e;
        int e_use = e;
        if( e_use>=0 ){
          //use each theory instantiator to instantiate f
          for( int i=0; i<theory::THEORY_LAST; i++ ){
            if( getQuantifiersEngine()->getInstantiator( i ) ){
              Debug("inst-engine-debug") << "Do " << getQuantifiersEngine()->getInstantiator( i )->identify() << " " << e_use << std::endl;
              int limitInst = 0;
              int quantStatus = getQuantifiersEngine()->getInstantiator( i )->doInstantiation( f, effort, e_use, limitInst );
              Debug("inst-engine-debug") << " -> status is " << quantStatus << std::endl;
              InstStrategy::updateStatus( d_inst_round_status, quantStatus );
            }
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if( getQuantifiersEngine()->hasAddedLemma() ){
      d_inst_round_status = InstStrategy::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "All instantiators finished, # added lemmas = ";
  Debug("inst-engine") << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
  //Notice() << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( !getQuantifiersEngine()->hasAddedLemma() ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( getQuantifiersEngine()->getInstantiator( i ) ){
        getQuantifiersEngine()->getInstantiator( i )->debugPrint("inst-engine-stuck");
        Debug("inst-engine-stuck") << std::endl;
      }
    }
    Debug("inst-engine-ctrl") << "---Fail." << std::endl;
    return false;
  }else{
    Debug("inst-engine-ctrl") << "---Done. " << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
#ifdef IE_PRINT_PROCESS_TIMES
    Notice() << "lemmas = " << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
#endif
    //flush lemmas to output channel
    getQuantifiersEngine()->flushLemmas( &d_th->getOutputChannel() );
    return true;
  }
}

int ierCounter = 0;

void InstantiationEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_FULL ){
    ierCounter++;
  }
  //determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if( Options::current()->instWhenMode==Options::INST_WHEN_FULL ){
    performCheck = ( e >= Theory::EFFORT_FULL );
  }else if( Options::current()->instWhenMode==Options::INST_WHEN_FULL_LAST_CALL ){
    performCheck = ( ( e==Theory::EFFORT_FULL  && ierCounter%2==0 ) || e==Theory::EFFORT_LAST_CALL );
  }else if( Options::current()->instWhenMode==Options::INST_WHEN_LAST_CALL ){
    performCheck = ( e >= Theory::EFFORT_LAST_CALL );
  }else{
    performCheck = true;
  }
  if( performCheck ){
    Debug("inst-engine") << "IE: Check " << e << " " << ierCounter << std::endl;
#ifdef IE_PRINT_PROCESS_TIMES
    double clSet = double(clock())/double(CLOCKS_PER_SEC);
    Notice() << "Run instantiation round " << e << " " << ierCounter << std::endl;
#endif
    bool quantActive = false;
    //for each quantifier currently asserted,
    // such that the counterexample literal is not in positive in d_counterexample_asserts
   // for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
    //  if( (*i).second ) {
    for( int i=0; i<(int)getQuantifiersEngine()->getNumAssertedQuantifiers(); i++ ){
      Node n = getQuantifiersEngine()->getAssertedQuantifier( i );
      if( Options::current()->cbqi && hasAddedCbqiLemma( n ) ){
        Node cel = d_ce_lit[ n ];
        bool active, value;
        bool ceValue = false;
        if( d_th->getValuation().hasSatValue( cel, value ) ){
          active = value;
          ceValue = true;
        }else{
          active = true;
        }
        getQuantifiersEngine()->setActive( n, active );
        if( active ){
          Debug("quantifiers") << "  Active : " << n;
          quantActive = true;
        }else{
          Debug("quantifiers") << "  NOT active : " << n;
          if( d_th->getValuation().isDecision( cel ) ){
            Debug("quant-req-phase") << "Bad decision : " << cel << std::endl;
          }
          //note that the counterexample literal must not be a decision
          Assert( !d_th->getValuation().isDecision( cel ) );
        }
        if( d_th->getValuation().hasSatValue( n, value ) ){
          Debug("quantifiers") << ", value = " << value;
        }
        if( ceValue ){
          Debug("quantifiers") << ", ce is asserted";
        }
        Debug("quantifiers") << std::endl;
      }else{
        getQuantifiersEngine()->setActive( n, true );
        quantActive = true;
        Debug("quantifiers") << "  Active : " << n << ", no ce assigned." << std::endl;
      }
      Debug("quantifiers-relevance")  << "Quantifier : " << n << std::endl;
      Debug("quantifiers-relevance")  << "   Relevance : " << getQuantifiersEngine()->getRelevance( n ) << std::endl;
      Debug("quantifiers") << "   Relevance : " << getQuantifiersEngine()->getRelevance( n ) << std::endl;
    }
    //}
    if( quantActive ){
      bool addedLemmas = doInstantiationRound( e );
      //Debug("quantifiers-dec") << "Do instantiation, level = " << d_th->getValuation().getDecisionLevel() << std::endl;
      //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      //  Debug("quantifiers-dec") << "   " << d_valuation.getDecision( i ) << std::endl;
      //}
      if( e==Theory::EFFORT_LAST_CALL ){
        if( !addedLemmas ){
          if( d_inst_round_status==InstStrategy::STATUS_SAT ){
            Debug("inst-engine") << "No instantiation given, returning SAT..." << std::endl;
            debugSat( SAT_INST_STRATEGY );
          }else{
            Debug("inst-engine") << "No instantiation given, returning unknown..." << std::endl;
            d_th->getOutputChannel().setIncomplete();
          }
        }
      }
    }else{
      if( e==Theory::EFFORT_LAST_CALL ){
        if( Options::current()->cbqi ){
          debugSat( SAT_CBQI );
        }
      }
    }
#ifdef IE_PRINT_PROCESS_TIMES
    double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
    Notice() << "Done Run instantiation round " << (clSet2-clSet) << std::endl;
#endif
  }
}

void InstantiationEngine::registerQuantifier( Node f ){
  //Notice() << "do cbqi " << f << " ? " << std::endl;
  Node ceBody = getQuantifiersEngine()->getCounterexampleBody( f );
  if( !doCbqi( f ) ){
    getQuantifiersEngine()->addTermToDatabase( ceBody, true );
    //need to tell which instantiators will be responsible
    //by default, just chose the UF instantiator
    getQuantifiersEngine()->getInstantiator( theory::THEORY_UF )->setHasConstraintsFrom( f );
  }

  //take into account user patterns
  if( f.getNumChildren()==3 ){
    Node subsPat = getQuantifiersEngine()->getSubstitutedNode( f[2], f );
    //add patterns
    for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
      //Notice() << "Add pattern " << subsPat[i] << " for " << f << std::endl;
      ((uf::InstantiatorTheoryUf*)getQuantifiersEngine()->getInstantiator( theory::THEORY_UF ))->addUserPattern( f, subsPat[i] );
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
  if( Options::current()->cbqiSetByUser ){
    return Options::current()->cbqi;
  }else if( Options::current()->cbqi ){
    //if quantifier has a non-arithmetic variable, then do not use cbqi
    //if quantifier has an APPLY_UF term, then do not use cbqi
    return !hasNonArithmeticVariable( f ) && !hasApplyUf( f[1] );
  }else{
    return false;
  }
}













//void InstantiationEngine::registerLiterals( Node n, Node f ){
//  if( n.getAttribute(InstConstantAttribute())==f ){
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      registerLiterals( n[i], f );
//    }
//    if( !d_ce_lit[ f ].isNull() ){
//      if( getQuantifiersEngine()->d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
//        if( n!=d_ce_lit[ f ] && n.notNode()!=d_ce_lit[ f ] ){
//          Debug("quant-dep-dec") << "Make " << n << " dependent on ";
//          Debug("quant-dep-dec") << d_ce_lit[ f ] << std::endl;
//          d_th->getOutputChannel().dependentDecision( d_ce_lit[ f ], n );
//        }
//      }
//    }
//  }
//}

void InstantiationEngine::debugSat( int reason ){
  if( reason==SAT_CBQI ){
    //Debug("quantifiers-sat") << "Decisions:" << std::endl;
    //for( int i=1; i<=(int)d_th->getValuation().getDecisionLevel(); i++ ){
    //  Debug("quantifiers-sat") << "   " << i << ": " << d_th->getValuation().getDecision( i ) << std::endl;
    //}
    //for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
    //  if( (*i).second ) {
    for( int i=0; i<(int)getQuantifiersEngine()->getNumAssertedQuantifiers(); i++ ){
      Node f = getQuantifiersEngine()->getAssertedQuantifier( i );
      Node cel = d_ce_lit[ f ];
      Assert( !cel.isNull() );
      bool value;
      if( d_th->getValuation().hasSatValue( cel, value ) ){
        if( !value ){
          AlwaysAssert(! d_th->getValuation().isDecision( cel ),
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

void InstantiationEngine::propagate( Theory::Effort level ){
  //propagate as decision all counterexample literals that are not asserted
  for( std::map< Node, Node >::iterator it = d_ce_lit.begin(); it != d_ce_lit.end(); ++it ){
    bool value;
    if( !d_th->getValuation().hasSatValue( it->second, value ) ){
      //if not already set, propagate as decision
      d_th->getOutputChannel().propagateAsDecision( it->second );
      Debug("cbqi-prop-as-dec") << "CBQI: propagate as decision " << it->second << std::endl;
    }
  }
}
