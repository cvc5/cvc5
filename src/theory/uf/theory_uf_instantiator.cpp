/*********************                                                        */
/*! \file theory_uf_instantiator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory uf instantiator class
 **/

#include "theory/uf/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/rewriterules/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/rewriterules/rr_candidate_generator.h"
#include "theory/rewriterules/efficient_e_matching.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {
namespace uf {

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* qe, Theory* th) :
Instantiator( c, qe, th )
{
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    //if( options::cbqi() ){
    //  addInstStrategy( new InstStrategyCheckCESolved( this, qe ) );
    //}
    //these are the instantiation strategies for basic E-matching
    if( options::userPatternsQuant() ){
      d_isup = new InstStrategyUserPatterns( this, qe );
      addInstStrategy( d_isup );
    }else{
      d_isup = NULL;
    }
    InstStrategyAutoGenTriggers* i_ag = new InstStrategyAutoGenTriggers( this, qe, Trigger::TS_ALL,
                                                                         InstStrategyAutoGenTriggers::RELEVANCE_DEFAULT, 3 );
    i_ag->setGenerateAdditional( true );
    addInstStrategy( i_ag );
    //addInstStrategy( new InstStrategyAddFailSplits( this, ie ) );
    if( !options::finiteModelFind() ){
      addInstStrategy( new InstStrategyFreeVariable( this, qe ) );
    }
    //d_isup->setPriorityOver( i_ag );
    //d_isup->setPriorityOver( i_agm );
    //i_ag->setPriorityOver( i_agm );
  }
}

void InstantiatorTheoryUf::preRegisterTerm( Node t ){
  //d_quantEngine->addTermToDatabase( t );
}

void InstantiatorTheoryUf::assertNode( Node assertion )
{
  Debug("quant-uf-assert") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  //preRegisterTerm( assertion );
  //INST_ELIM_TRY//d_quantEngine->addTermToDatabase( assertion );
  if( options::cbqi() ){
    if( assertion.hasAttribute(InstConstantAttribute()) ){
      setQuantifierActive( assertion.getAttribute(InstConstantAttribute()) );
    }else if( assertion.getKind()==NOT && assertion[0].hasAttribute(InstConstantAttribute()) ){
      setQuantifierActive( assertion[0].getAttribute(InstConstantAttribute()) );
    }
  }
}

void InstantiatorTheoryUf::addUserPattern( Node f, Node pat ){
  if( d_isup ){
    d_isup->addUserPattern( f, pat );
    setQuantifierActive( f );
  }
}


void InstantiatorTheoryUf::processResetInstantiationRound( Theory::Effort effort ){
  //d_ground_reps.clear();
}

int InstantiatorTheoryUf::process( Node f, Theory::Effort effort, int e ){
  Debug("quant-uf") << "UF: Try to solve (" << e << ") for " << f << "... " << std::endl;
  return InstStrategy::STATUS_SAT;
}

void InstantiatorTheoryUf::debugPrint( const char* c )
{

}

bool InstantiatorTheoryUf::hasTerm( Node a ){
  return ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a );
}

bool InstantiatorTheoryUf::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool InstantiatorTheoryUf::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

Node InstantiatorTheoryUf::getRepresentative( Node a ){
  if( hasTerm( a ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}

eq::EqualityEngine* InstantiatorTheoryUf::getEqualityEngine(){
  return &((TheoryUF*)d_th)->d_equalityEngine;
}

void InstantiatorTheoryUf::getEquivalenceClass( Node a, std::vector< Node >& eqc ){
  if( hasTerm( a ) ){
    a = getEqualityEngine()->getRepresentative( a );
    eq::EqClassIterator eqc_iter( a, getEqualityEngine() );
    while( !eqc_iter.isFinished() ){
      if( std::find( eqc.begin(), eqc.end(), *eqc_iter )==eqc.end() ){
        eqc.push_back( *eqc_iter );
      }
      eqc_iter++;
    }
  }
}

void InstantiatorTheoryUf::outputEqClass( const char* c, Node n ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
    eq::EqClassIterator eqc_iter( getRepresentative( n ),
                                  &((TheoryUF*)d_th)->d_equalityEngine );
    bool firstTime = true;
    while( !eqc_iter.isFinished() ){
      if( !firstTime ){ Debug(c) << ", "; }
      Debug(c) << (*eqc_iter);
      firstTime = false;
      eqc_iter++;
    }
  }else{
    Debug(c) << n;
  }
}

rrinst::CandidateGenerator* InstantiatorTheoryUf::getRRCanGenClasses(){
  uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(getTheory());
  eq::EqualityEngine* ee = static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());
  return new eq::rrinst::CandidateGeneratorTheoryEeClasses(ee);
}

rrinst::CandidateGenerator* InstantiatorTheoryUf::getRRCanGenClass(){
  uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(getTheory());
  eq::EqualityEngine* ee = static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());
  return new eq::rrinst::CandidateGeneratorTheoryEeClass(ee);
}


} /* namespace uf */
} /* namespace theory */
} /* namespace cvc4 */
