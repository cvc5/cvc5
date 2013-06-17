/*********************                                                        */
/*! \file bounded_integers.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite engine module
 **
 ** This class manages rewrite rules for quantifiers
 **/

#include "theory/quantifiers/rewrite_engine.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/inst_match_generator.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

RewriteEngine::RewriteEngine( context::Context* c, QuantifiersEngine* qe ) : QuantifiersModule(qe) {

}

void RewriteEngine::check( Theory::Effort e ) {
  if( e==Theory::EFFORT_FULL ){
    //apply rewrite rules
    int addedLemmas = 0;
    for( unsigned i=0; i<d_rr_quant.size(); i++ ) {
      addedLemmas += checkRewriteRule( d_rr_quant[i] );
    }
    Trace("rewrite-engine") << "Rewrite engine generated " << addedLemmas << " lemmas." << std::endl;
    if (addedLemmas==0) {
    }else{
      //otherwise, the search will continue
      d_quantEngine->flushLemmas( &d_quantEngine->getOutputChannel() );
    }
  }
}

int RewriteEngine::checkRewriteRule( Node f ) {
  Trace("rewrite-engine-inst") << "Check " << f << "..." << std::endl;
  int addedLemmas = 0;
  //reset triggers
  Node rr = f.getAttribute(QRewriteRuleAttribute());
  if( d_rr_triggers.find(f)==d_rr_triggers.end() ){
    std::vector< inst::Trigger * > triggers;
    if( f.getNumChildren()==3 ){
      for(unsigned i=0; i<f[2].getNumChildren(); i++ ){
        Node pat = f[2][i];
        std::vector< Node > nodes;
        Trace("rewrite-engine-trigger") << "Trigger is : ";
        for( int j=0; j<(int)pat.getNumChildren(); j++ ){
          Node p = d_quantEngine->getTermDatabase()->getInstConstantNode( pat[j], f );
          nodes.push_back( p );
          Trace("rewrite-engine-trigger") << p << " " << p.getKind() << " ";
        }
        Trace("rewrite-engine-trigger") << std::endl;
        Assert( inst::Trigger::isUsableTrigger( nodes, f ) );
        inst::Trigger * tr = inst::Trigger::mkTrigger( d_quantEngine, f, nodes, 0, true, inst::Trigger::TR_MAKE_NEW, false );
        tr->getGenerator()->setActiveAdd(false);
        triggers.push_back( tr );
      }
    }
    d_rr_triggers[f].insert( d_rr_triggers[f].end(), triggers.begin(), triggers.end() );
  }
  for( unsigned i=0; i<d_rr_triggers[f].size(); i++ ){
    Trace("rewrite-engine-inst") << "Try trigger " << *d_rr_triggers[f][i] << std::endl;
    d_rr_triggers[f][i]->resetInstantiationRound();
    d_rr_triggers[f][i]->reset( Node::null() );
    bool success;
    do
    {
      InstMatch m;
      success = d_rr_triggers[f][i]->getNextMatch( f, m );
      if( success ){
        //see if instantiation is true in the model
        bool trueInModel = false;

        if( !trueInModel ){
          Trace("rewrite-engine-inst") << "Add instantiation : " << m << std::endl;
          if( d_quantEngine->addInstantiation( f, m ) ){
            addedLemmas++;
            Trace("rewrite-engine-inst-debug") << "success" << std::endl;
          }else{
            Trace("rewrite-engine-inst-debug") << "failure." << std::endl;
          }
        }
      }
    }while(success);
  }
  Trace("rewrite-engine-inst") << "Rule " << f << " generated " << addedLemmas << " lemmas." << std::endl;
  return addedLemmas;
}

void RewriteEngine::registerQuantifier( Node f ) {
  if( f.hasAttribute(QRewriteRuleAttribute()) ){
    Trace("rewrite-engine") << "Register quantifier " << f << std::endl;
    Node rr = f.getAttribute(QRewriteRuleAttribute());
    Trace("rewrite-engine") << "  rewrite rule is : " << rr << std::endl;
    d_rr_quant.push_back( f );
  }
}

void RewriteEngine::assertNode( Node n ) {

}

