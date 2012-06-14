/*********************                                                        */
/*! \file quantifiers_engine.cpp
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
 ** \brief Implementation of quantifiers engine class
 **/

#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

//#define COMPUTE_RELEVANCE
//#define REWRITE_ASSERTED_QUANTIFIERS

  /** reset instantiation */
void InstStrategy::resetInstantiationRound( Theory::Effort effort ){
  d_no_instantiate_temp.clear();
  d_no_instantiate_temp.insert( d_no_instantiate_temp.begin(), d_no_instantiate.begin(), d_no_instantiate.end() );
  processResetInstantiationRound( effort );
}
/** do instantiation round method */
int InstStrategy::doInstantiation( Node f, Theory::Effort effort, int e, int limitInst ){
  if( shouldInstantiate( f ) ){
    int origLemmas = d_quantEngine->getNumLemmasWaiting();
    int retVal = process( f, effort, e, limitInst );
    if( d_quantEngine->getNumLemmasWaiting()!=origLemmas ){
      for( int i=0; i<(int)d_priority_over.size(); i++ ){
        d_priority_over[i]->d_no_instantiate_temp.push_back( f );
      }
    }
    return retVal;
  }else{
    return STATUS_UNKNOWN;
  }
}

bool TermArgTrie::addTerm2( QuantifiersEngine* qe, Node n, int argIndex ){
  if( argIndex<(int)n.getNumChildren() ){
    Node r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
    std::map< Node, TermArgTrie >::iterator it = d_data.find( r );
    if( it==d_data.end() ){
      d_data[r].addTerm2( qe, n, argIndex+1 );
      return true;
    }else{
      return it->second.addTerm2( qe, n, argIndex+1 );
    }
  }else{
    //store n in d_data (this should be interpretted as the "data" and not as a reference to a child)
    d_data[n].d_data.clear();
    return false;
  }
}

void TermDb::addTerm( Node n, std::vector< Node >& added, bool withinQuant ){
  //don't add terms in quantifier bodies
  if( !withinQuant || Options::current()->registerQuantBodyTerms ){
    if( d_processed.find( n )==d_processed.end() ){
      d_processed[n] = true;
      //if this is an atomic trigger, consider adding it
      if( Trigger::isAtomicTrigger( n ) ){
        if( !n.hasAttribute(InstConstantAttribute()) ){
          Debug("term-db") << "register trigger term " << n << std::endl;
          //Notice() << "register trigger term " << n << std::endl;
          Node op = n.getOperator();
          d_op_map[op].push_back( n );
          d_type_map[ n.getType() ].push_back( n );
          added.push_back( n );

          uf::InstantiatorTheoryUf* d_ith = (uf::InstantiatorTheoryUf*)d_quantEngine->getInstantiator( THEORY_UF );
          for( int i=0; i<(int)n.getNumChildren(); i++ ){
            addTerm( n[i], added, withinQuant );
            if( Options::current()->efficientEMatching ){
              if( d_parents[n[i]][op].empty() ){
                //must add parent to equivalence class info
                Node nir = d_ith->getRepresentative( n[i] );
                uf::EqClassInfo* eci_nir = d_ith->getEquivalenceClassInfo( nir );
                if( eci_nir ){
                  eci_nir->d_pfuns[ op ] = true;
                }
              }
              //add to parent structure
              if( std::find( d_parents[n[i]][op][i].begin(), d_parents[n[i]][op][i].end(), n )==d_parents[n[i]][op][i].end() ){
                d_parents[n[i]][op][i].push_back( n );
              }
            }
          }
          if( Options::current()->efficientEMatching ){
            //new term, add n to candidate generators
            for( int i=0; i<(int)d_ith->d_cand_gens[op].size(); i++ ){
              d_ith->d_cand_gens[op][i]->addCandidate( n );
            }
          }
          if( Options::current()->eagerInstQuant ){
            if( !n.hasAttribute(InstLevelAttribute()) && n.getAttribute(InstLevelAttribute())==0 ){
              int addedLemmas = 0;
              for( int i=0; i<(int)d_ith->d_op_triggers[op].size(); i++ ){
                addedLemmas += d_ith->d_op_triggers[op][i]->addTerm( n );
              }
              //Message() << "Terms, added lemmas: " << addedLemmas << std::endl;
              d_quantEngine->flushLemmas( &d_quantEngine->getTheoryEngine()->getTheory( THEORY_QUANTIFIERS )->getOutputChannel() );
            }
          }
        }
      }
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        addTerm( n[i], added, withinQuant );
      }
    }
  }
}

void TermDb::reset( Theory::Effort effort ){
  int nonCongruentCount = 0;
  int congruentCount = 0;
  int alreadyCongruentCount = 0;
  //rebuild d_func/pred_map_trie for each operation, this will calculate all congruent terms
  for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
    if( !it->second.empty() ){
      if( it->second[0].getType()==NodeManager::currentNM()->booleanType() ){
        d_pred_map_trie[ 0 ][ it->first ].d_data.clear();
        d_pred_map_trie[ 1 ][ it->first ].d_data.clear();
      }else{
        d_func_map_trie[ it->first ].d_data.clear();
        for( int i=0; i<(int)it->second.size(); i++ ){
          Node n = it->second[i];
          if( !n.getAttribute(NoMatchAttribute()) ){
            if( !d_func_map_trie[ it->first ].addTerm( d_quantEngine, n ) ){
              NoMatchAttribute nma;
              n.setAttribute(nma,true);
              congruentCount++;
            }else{
              nonCongruentCount++;
            }
          }else{
            congruentCount++;
            alreadyCongruentCount++;
          }
        }
      }
    }
  }
  for( int i=0; i<2; i++ ){
    Node n = NodeManager::currentNM()->mkConst( i==1 );
    eq::EqClassIterator eqc( d_quantEngine->getEqualityQuery()->getRepresentative( n ),
                              ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
    while( !eqc.isFinished() ){
      Node en = (*eqc);
      if( en.getKind()==APPLY_UF && !en.hasAttribute(InstConstantAttribute()) ){
        if( !en.getAttribute(NoMatchAttribute()) ){
          Node op = en.getOperator();
          if( !d_pred_map_trie[i][op].addTerm( d_quantEngine, en ) ){
            NoMatchAttribute nma;
            en.setAttribute(nma,true);
            congruentCount++;
          }else{
            nonCongruentCount++;
          }
        }else{
          alreadyCongruentCount++;
        }
      }
      ++eqc;
    }
  }
  Debug("term-db-cong") << "TermDb: Reset" << std::endl;
  Debug("term-db-cong") << "Congruent/Non-Congruent = ";
  Debug("term-db-cong") << congruentCount << "(" << alreadyCongruentCount << ") / " << nonCongruentCount << std::endl;
}



QuantifiersEngine::QuantifiersEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_forall_asserts( c ),
d_active( c ){
  d_eq_query = NULL;
  d_term_db = new TermDb( this );
}

Instantiator* QuantifiersEngine::getInstantiator( int id ){
  return d_te->getTheory( id )->getInstantiator();
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_time);

  if( e==Theory::EFFORT_LAST_CALL ){
    ++(d_statistics.d_instantiation_rounds_lc);
  }else if( e==Theory::EFFORT_FULL ){
    ++(d_statistics.d_instantiation_rounds);
  }
  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->check( e );
  }
  //if( e==Theory::EFFORT_FULL ){
  //  Notice() << "Done instantiation Round" << std::endl;
  //}
}

std::vector<Node> QuantifiersEngine::createInstVariable( std::vector<Node> & vars ){
  std::vector<Node> inst_constant;
  inst_constant.reserve(vars.size());
  for( std::vector<Node>::const_iterator v = vars.begin();
       v != vars.end(); ++v ){
    //make instantiation constants
    Node ic = NodeManager::currentNM()->mkInstConstant( (*v).getType() );
    inst_constant.push_back( ic );
  };
  return inst_constant;
}

void QuantifiersEngine::makeInstantiationConstantsFor( Node f ){
  if( d_inst_constants.find( f )==d_inst_constants.end() ){
    Debug("quantifiers-engine") << "Instantiation constants for " << f << " : " << std::endl;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      d_vars[f].push_back( f[0][i] );
      //make instantiation constants
      Node ic = NodeManager::currentNM()->mkInstConstant( f[0][i].getType() );
      d_inst_constants_map[ic] = f;
      d_inst_constants[ f ].push_back( ic );
      Debug("quantifiers-engine") << "  " << ic << std::endl;
      //set the var number attribute
      InstVarNumAttribute ivna;
      ic.setAttribute(ivna,i);
    }
  }
}

void QuantifiersEngine::registerQuantifier( Node f ){
  if( std::find( d_quants.begin(), d_quants.end(), f )==d_quants.end() ){
    std::vector< Node > quants;
#ifdef REWRITE_ASSERTED_QUANTIFIERS
    //do assertion-time rewriting of quantifier
    Node nf = quantifiers::QuantifiersRewriter::rewriteQuant( f, false, false );
    if( nf!=f ){
      Debug("quantifiers-rewrite") << "*** assert-rewrite " << f << std::endl;
      Debug("quantifiers-rewrite") << " to " << std::endl;
      Debug("quantifiers-rewrite") << nf << std::endl;
      //we will instead register all the rewritten quantifiers
      if( nf.getKind()==FORALL ){
        quants.push_back( nf );
      }else if( nf.getKind()==AND ){
        for( int i=0; i<(int)nf.getNumChildren(); i++ ){
          quants.push_back( nf[i] );
        }
      }else{
        //unhandled: rewrite must go to a quantifier, or conjunction of quantifiers
        Assert( false );
      }
    }else{
      quants.push_back( f );
    }
#else
    quants.push_back( f );
#endif
    for( int q=0; q<(int)quants.size(); q++ ){
      d_quant_rewritten[f].push_back( quants[q] );
      d_rewritten_quant[ quants[q] ] = f;
      ++(d_statistics.d_num_quant);
      Assert( quants[q].getKind()==FORALL );
      //register quantifier
      d_quants.push_back( quants[q] );
      //make instantiation constants for quants[q]
      makeInstantiationConstantsFor( quants[q] );
      //compute symbols in quants[q]
      std::vector< Node > syms;
      computeSymbols( quants[q][1], syms );
      d_syms[quants[q]].insert( d_syms[quants[q]].begin(), syms.begin(), syms.end() );
      //set initial relevance
      int minRelevance = -1;
      for( int i=0; i<(int)syms.size(); i++ ){
        d_syms_quants[ syms[i] ].push_back( quants[q] );
        int r = getRelevance( syms[i] );
        if( r!=-1 && ( minRelevance==-1 || r<minRelevance ) ){
          minRelevance = r;
        }
      }
#ifdef COMPUTE_RELEVANCE
      if( minRelevance!=-1 ){
        setRelevance( quants[q], minRelevance+1 );
      }
#endif
      //register with each module
      for( int i=0; i<(int)d_modules.size(); i++ ){
        d_modules[i]->registerQuantifier( quants[q] );
      }
      Node ceBody = getCounterexampleBody( quants[q] );
      generatePhaseReqs( quants[q], ceBody );
      //also register it with the strong solver
      if( Options::current()->finiteModelFind ){
        ((uf::TheoryUF*)d_te->getTheory( THEORY_UF ))->getStrongSolver()->registerQuantifier( quants[q] );
      }
    }
  }
}

void QuantifiersEngine::registerPattern( std::vector<Node> & pattern) {
  for(std::vector<Node>::iterator p = pattern.begin(); p != pattern.end(); ++p){
    std::vector< Node > added;
    d_term_db->addTerm(*p,added);
  }
}

void QuantifiersEngine::assertNode( Node f ){
  Assert( f.getKind()==FORALL );
  for( int j=0; j<(int)d_quant_rewritten[f].size(); j++ ){
    d_forall_asserts.push_back( d_quant_rewritten[f][j] );
    for( int i=0; i<(int)d_modules.size(); i++ ){
      d_modules[i]->assertNode( d_quant_rewritten[f][j] );
    }
  }
}

void QuantifiersEngine::propagate( Theory::Effort level ){
  CodeTimer codeTimer(d_time);

  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->propagate( level );
  }
}

void QuantifiersEngine::addTermToDatabase( Node n, bool withinQuant ){
  if( d_term_db ){
    std::vector< Node > added;
    d_term_db->addTerm( n, added, withinQuant );
#ifdef COMPUTE_RELEVANCE
    for( int i=0; i<(int)added.size(); i++ ){
      if( !withinQuant ){
        setRelevance( added[i].getOperator(), 0 );
      }
    }
#endif
  }else{
    Notice() << "Warning: no term database for quantifier engine." << std::endl;
  }
}

bool QuantifiersEngine::addLemma( Node lem ){
  //AJR: the following check is necessary until FULL_CHECK is guarenteed after d_out->lemma(...)
  Debug("inst-engine-debug") << "Adding lemma : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if( d_lemmas_produced.find( lem )==d_lemmas_produced.end() ){
    //d_curr_out->lemma( lem );
    d_lemmas_produced[ lem ] = true;
    d_lemmas_waiting.push_back( lem );
    Debug("inst-engine-debug") << "Added lemma : " << lem << std::endl;
    return true;
  }else{
    Debug("inst-engine-debug") << "Duplicate." << std::endl;
    return false;
  }
}

bool QuantifiersEngine::addInstantiation( Node f, std::vector< Node >& terms )
{
    //Notice() << "***& Instantiate " << f << " with " << std::endl;
    //for( int i=0; i<(int)terms.size(); i++ ){
    //  Notice() << "   " << terms[i] << std::endl;
    //}
  Assert( f.getKind()==FORALL );
  Assert( !f.hasAttribute(InstConstantAttribute()) );
  Assert( d_vars[f].size()==terms.size() && d_vars[f].size()==f[0].getNumChildren() );
  Node body = f[ 1 ].substitute( d_vars[f].begin(), d_vars[f].end(),
                                 terms.begin(), terms.end() );
  NodeBuilder<> nb(kind::OR);
  nb << d_rewritten_quant[f].notNode() << body;
  Node lem = nb;
  if( addLemma( lem ) ){
    //Notice() << "     Added lemma : " << body << std::endl;
    //Notice() << "***& Instantiate " << f << " with " << std::endl;
    //for( int i=0; i<(int)terms.size(); i++ ){
    //  Notice() << "   " << terms[i] << std::endl;
    //}

    //Notice() << "**INST" << std::endl;
    Debug("inst") << "*** Instantiate " << f << " with " << std::endl;
    //Notice() << "*** Instantiate " << f << " with " << std::endl;
    uint64_t maxInstLevel = 0;
    for( int i=0; i<(int)terms.size(); i++ ){
      if( terms[i].hasAttribute(InstConstantAttribute()) ){
        Debug("inst")<< "***& Bad Instantiate " << f << " with " << std::endl;
        for( int i=0; i<(int)terms.size(); i++ ){
          Debug("inst") << "   " << terms[i] << std::endl;
        }
        Unreachable("Bad instantiation");
      }else{
        Debug("inst") << "   " << terms[i];
        //Notice() << "   " << terms[i] << std::endl;
        //Debug("inst-engine") << " " << terms[i].getAttribute(InstLevelAttribute());
        Debug("inst") << std::endl;
        if( terms[i].hasAttribute(InstLevelAttribute()) ){
          if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
            maxInstLevel = terms[i].getAttribute(InstLevelAttribute());
          }
        }else{
          setInstantiationLevelAttr( terms[i], 0 );
        }
      }
    }
    setInstantiationLevelAttr( body, maxInstLevel+1 );
    ++(d_statistics.d_instantiations);
    d_statistics.d_total_inst_var += (int)terms.size();
    d_statistics.d_max_instantiation_level.maxAssign( maxInstLevel+1 );
    return true;
  }else{
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
}

bool QuantifiersEngine::addInstantiation( Node f, InstMatch& m, bool addSplits ){
  m.makeComplete( f, this );
  m.makeRepresentative( this );
  Debug("quant-duplicate") << "After make rep: " << m << std::endl;
  if( !d_inst_match_trie[f].addInstMatch( this, f, m, true ) ){
    Debug("quant-duplicate") << " -> Already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
  Debug("quant-duplicate") << " -> Does not exist." << std::endl;
  std::vector< Node > match;
  m.computeTermVec( d_inst_constants[f], match );

  //old....
  //m.makeRepresentative( d_eq_query );
  //std::vector< Node > match;
  //m.computeTermVec( this, d_inst_constants[f], match );

  //Notice() << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
  //for( int i=0; i<(int)m->d_match.size(); i++ ){
  //  Notice() << "   " << m->d_match[i] << std::endl;
  //}

  if( addInstantiation( f, match ) ){
    //d_statistics.d_total_inst_var_unspec.setData( d_statistics.d_total_inst_var_unspec.getData() + (int)d_inst_constants[f].size() - m.d_map.size()/2 );
    //if( d_inst_constants[f].size()!=m.d_map.size() ){
    //  //Notice() << "Unspec. " << std::endl;
    //  //Notice() << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
    //  //for( int i=0; i<(int)m->d_match.size(); i++ ){
    //  //  Notice() << "   " << m->d_match[i] << std::endl;
    //  //}
    //  ++(d_statistics.d_inst_unspec);
    //}
    //if( addSplits ){
    //  for( std::map< Node, Node >::iterator it = m->d_splits.begin(); it != m->d_splits.end(); ++it ){
    //    addSplitEquality( it->first, it->second, true, true );
    //  }
    //}
    return true;
  }
  return false;
}

bool QuantifiersEngine::addSplit( Node n, bool reqPhase, bool reqPhasePol ){
  n = Rewriter::rewrite( n );
  Node lem = NodeManager::currentNM()->mkNode( OR, n, n.notNode() );
  if( addLemma( lem ) ){
    ++(d_statistics.d_splits);
    Debug("inst") << "*** Add split " << n<< std::endl;
    //if( reqPhase ){
    //  d_curr_out->requirePhase( n, reqPhasePol );
    //}
    return true;
  }
  return false;
}

bool QuantifiersEngine::addSplitEquality( Node n1, Node n2, bool reqPhase, bool reqPhasePol ){
  //Assert( !n1.hasAttribute(InstConstantAttribute()) );
  //Assert( !n2.hasAttribute(InstConstantAttribute()) );
  //Assert( !areEqual( n1, n2 ) );
  //Assert( !areDisequal( n1, n2 ) );
  Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node fm = NodeManager::currentNM()->mkNode( knd, n1, n2 );
  return addSplit( fm );
}

void QuantifiersEngine::flushLemmas( OutputChannel* out ){
  for( int i=0; i<(int)d_lemmas_waiting.size(); i++ ){
    out->lemma( d_lemmas_waiting[i] );
  }
  d_lemmas_waiting.clear();
}

Node QuantifiersEngine::getCounterexampleBody( Node f ){
  std::map< Node, Node >::iterator it = d_counterexample_body.find( f );
  if( it==d_counterexample_body.end() ){
    makeInstantiationConstantsFor( f );
    Node n = getSubstitutedNode( f[1], f );
    d_counterexample_body[ f ] = n;
    return n;
  }else{
    return it->second;
  }
}

Node QuantifiersEngine::getSkolemizedBody( Node f ){
  Assert( f.getKind()==FORALL );
  if( d_skolem_body.find( f )==d_skolem_body.end() ){
    std::vector< Node > vars;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      Node skv = NodeManager::currentNM()->mkSkolem( f[0][i].getType() );
      d_skolem_constants[ f ].push_back( skv );
      vars.push_back( f[0][i] );
    }
    d_skolem_body[ f ] = f[ 1 ].substitute( vars.begin(), vars.end(),
                                            d_skolem_constants[ f ].begin(), d_skolem_constants[ f ].end() );
    if( f.hasAttribute(InstLevelAttribute()) ){
      setInstantiationLevelAttr( d_skolem_body[ f ], f.getAttribute(InstLevelAttribute()) );
    }
  }
  return d_skolem_body[ f ];
}

void QuantifiersEngine::getPhaseReqTerms( Node f, std::vector< Node >& nodes ){
  if( Options::current()->literalMatchMode!=Options::LITERAL_MATCH_NONE ){
    bool printed = false;
    // doing literal-based matching (consider polarity of literals)
    for( int i=0; i<(int)nodes.size(); i++ ){
      Node prev = nodes[i];
      bool nodeChanged = false;
      if( isPhaseReq( f, nodes[i] ) ){
        bool preq = getPhaseReq( f, nodes[i] );
        nodes[i] = NodeManager::currentNM()->mkNode( IFF, nodes[i], NodeManager::currentNM()->mkConst<bool>(preq) );
        nodeChanged = true;
      }
      //else if( qe->isPhaseReqEquality( f, trNodes[i] ) ){
      //  Node req = qe->getPhaseReqEquality( f, trNodes[i] );
      //  trNodes[i] = NodeManager::currentNM()->mkNode( EQUAL, trNodes[i], req );
      //}
      if( nodeChanged ){
        if( !printed ){
          Debug("literal-matching") << "LitMatch for " << f << ":" << std::endl;
          printed = true;
        }
        Debug("literal-matching") << "  Make " << prev << " -> " << nodes[i] << std::endl;
        Assert( prev.hasAttribute(InstConstantAttribute()) );
        setInstantiationConstantAttr( nodes[i], prev.getAttribute(InstConstantAttribute()) );
        ++(d_statistics.d_lit_phase_req);
      }else{
        ++(d_statistics.d_lit_phase_nreq);
      }
    }
  }else{
    d_statistics.d_lit_phase_nreq += (int)nodes.size();
  }
}

void QuantifiersEngine::computePhaseReqs2( Node n, bool polarity, std::map< Node, int >& phaseReqs ){
  bool newReqPol = false;
  bool newPolarity;
  if( n.getKind()==NOT ){
    newReqPol = true;
    newPolarity = !polarity;
  }else if( n.getKind()==OR || n.getKind()==IMPLIES ){
    if( !polarity ){
      newReqPol = true;
      newPolarity = false;
    }
  }else if( n.getKind()==AND ){
    if( polarity ){
      newReqPol = true;
      newPolarity = true;
    }
  }else{
    int val = polarity ? 1 : -1;
    if( phaseReqs.find( n )==phaseReqs.end() ){
      phaseReqs[n] = val;
    }else if( val!=phaseReqs[n] ){
      phaseReqs[n] = 0;
    }
  }
  if( newReqPol ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n.getKind()==IMPLIES && i==0 ){
        computePhaseReqs2( n[i], !newPolarity, phaseReqs );
      }else{
        computePhaseReqs2( n[i], newPolarity, phaseReqs );
      }
    }
  }
}

void QuantifiersEngine::computePhaseReqs( Node n, bool polarity, std::map< Node, bool >& phaseReqs ){
  std::map< Node, int > phaseReqs2;
  computePhaseReqs2( n, polarity, phaseReqs2 );
  for( std::map< Node, int >::iterator it = phaseReqs2.begin(); it != phaseReqs2.end(); ++it ){
    if( it->second==1 ){
      phaseReqs[ it->first ] = true;
    }else if( it->second==-1 ){
      phaseReqs[ it->first ] = false;
    }
  }
}

void QuantifiersEngine::generatePhaseReqs( Node f, Node n ){
  computePhaseReqs( n, false, d_phase_reqs[f] );
  Debug("inst-engine-phase-req") << "Phase requirements for " << f << ":" << std::endl;
  //now, compute if any patterns are equality required
  for( std::map< Node, bool >::iterator it = d_phase_reqs[f].begin(); it != d_phase_reqs[f].end(); ++it ){
    Debug("inst-engine-phase-req") << "   " << it->first << " -> " << it->second << std::endl;
    if( it->first.getKind()==EQUAL ){
      if( it->first[0].hasAttribute(InstConstantAttribute()) ){
        if( !it->first[1].hasAttribute(InstConstantAttribute()) ){
          d_phase_reqs_equality_term[f][ it->first[0] ] = it->first[1];
          d_phase_reqs_equality[f][ it->first[0] ] = it->second;
          Debug("inst-engine-phase-req") << "      " << it->first[0] << ( it->second ? " == " : " != " ) << it->first[1] << std::endl;
        }
      }else if( it->first[1].hasAttribute(InstConstantAttribute()) ){
        d_phase_reqs_equality_term[f][ it->first[1] ] = it->first[0];
        d_phase_reqs_equality[f][ it->first[1] ] = it->second;
        Debug("inst-engine-phase-req") << "      " << it->first[1] << ( it->second ? " == " : " != " ) << it->first[0] << std::endl;
      }
    }
  }

}

Node QuantifiersEngine::getSubstitutedNode( Node n, Node f ){
  return convertNodeToPattern(n,f,d_vars[f],d_inst_constants[ f ]);
}

Node QuantifiersEngine::convertNodeToPattern( Node n, Node f, const std::vector<Node> & vars,
                                              const std::vector<Node> & inst_constants){
  Node n2 = n.substitute( vars.begin(), vars.end(),
                          inst_constants.begin(),
                          inst_constants.end() );
  setInstantiationConstantAttr( n2, f );
  return n2;
}


void QuantifiersEngine::setInstantiationLevelAttr( Node n, uint64_t level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setInstantiationLevelAttr( n[i], level );
  }
}


void QuantifiersEngine::setInstantiationConstantAttr( Node n, Node f ){
  if( !n.hasAttribute(InstConstantAttribute()) ){
    bool setAttr = false;
    if( n.getKind()==INST_CONSTANT ){
      setAttr = true;
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        setInstantiationConstantAttr( n[i], f );
        if( n[i].hasAttribute(InstConstantAttribute()) ){
          setAttr = true;
        }
      }
    }
    if( setAttr ){
      InstConstantAttribute ica;
      n.setAttribute(ica,f);
      //also set the no-match attribute
      NoMatchAttribute nma;
      n.setAttribute(nma,true);
    }
  }
}

QuantifiersEngine::Statistics::Statistics():
  d_num_quant("QuantifiersEngine::Num_Quantifiers", 0),
  d_instantiation_rounds("QuantifiersEngine::Rounds_Instantiation_Full", 0),
  d_instantiation_rounds_lc("QuantifiersEngine::Rounds_Instantiation_Last_Call", 0),
  d_instantiations("QuantifiersEngine::Instantiations_Total", 0),
  d_max_instantiation_level("QuantifiersEngine::Max_Instantiation_Level", 0),
  d_splits("QuantifiersEngine::Total_Splits", 0),
  d_total_inst_var("QuantifiersEngine::Vars_Inst", 0),
  d_total_inst_var_unspec("QuantifiersEngine::Vars_Inst_Unspecified", 0),
  d_inst_unspec("QuantifiersEngine::Unspecified_Inst", 0),
  d_inst_duplicate("QuantifiersEngine::Duplicate_Inst", 0),
  d_lit_phase_req("QuantifiersEngine::lit_phase_req", 0),
  d_lit_phase_nreq("QuantifiersEngine::lit_phase_nreq", 0),
  d_triggers("QuantifiersEngine::Triggers", 0),
  d_simple_triggers("QuantifiersEngine::Triggers_Simple", 0),
  d_multi_triggers("QuantifiersEngine::Triggers_Multi", 0),
  d_multi_trigger_instantiations("QuantifiersEngine::Multi_Trigger_Instantiations", 0)
{
  StatisticsRegistry::registerStat(&d_num_quant);
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
  StatisticsRegistry::registerStat(&d_instantiation_rounds_lc);
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_max_instantiation_level);
  StatisticsRegistry::registerStat(&d_splits);
  StatisticsRegistry::registerStat(&d_total_inst_var);
  StatisticsRegistry::registerStat(&d_total_inst_var_unspec);
  StatisticsRegistry::registerStat(&d_inst_unspec);
  StatisticsRegistry::registerStat(&d_inst_duplicate);
  StatisticsRegistry::registerStat(&d_lit_phase_req);
  StatisticsRegistry::registerStat(&d_lit_phase_nreq);
  StatisticsRegistry::registerStat(&d_triggers);
  StatisticsRegistry::registerStat(&d_simple_triggers);
  StatisticsRegistry::registerStat(&d_multi_triggers);
  StatisticsRegistry::registerStat(&d_multi_trigger_instantiations);
}

QuantifiersEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_num_quant);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds_lc);
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_max_instantiation_level);
  StatisticsRegistry::unregisterStat(&d_splits);
  StatisticsRegistry::unregisterStat(&d_total_inst_var);
  StatisticsRegistry::unregisterStat(&d_total_inst_var_unspec);
  StatisticsRegistry::unregisterStat(&d_inst_unspec);
  StatisticsRegistry::unregisterStat(&d_inst_duplicate);
  StatisticsRegistry::unregisterStat(&d_lit_phase_req);
  StatisticsRegistry::unregisterStat(&d_lit_phase_nreq);
  StatisticsRegistry::unregisterStat(&d_triggers);
  StatisticsRegistry::unregisterStat(&d_simple_triggers);
  StatisticsRegistry::unregisterStat(&d_multi_triggers);
  StatisticsRegistry::unregisterStat(&d_multi_trigger_instantiations);
}

Node QuantifiersEngine::getFreeVariableForInstConstant( Node n ){
  TypeNode tn = n.getType();
  if( d_free_vars.find( tn )==d_free_vars.end() ){
    //if integer or real, make zero
    if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
      Rational z(0);
      d_free_vars[tn] = NodeManager::currentNM()->mkConst( z );
    }else{
      if( d_term_db->d_type_map[ tn ].empty() ){
        d_free_vars[tn] = NodeManager::currentNM()->mkVar( tn );
      }else{
        d_free_vars[tn] =d_term_db->d_type_map[ tn ][ 0 ];
      }
    }
  }
  return d_free_vars[tn];
}

/** compute symbols */
void QuantifiersEngine::computeSymbols( Node n, std::vector< Node >& syms ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( std::find( syms.begin(), syms.end(), op )==syms.end() ){
      syms.push_back( op );
    }
  }
  if( n.getKind()!=FORALL ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeSymbols( n[i], syms );
    }
  }
}

/** set relevance */
void QuantifiersEngine::setRelevance( Node s, int r ){
  int rOld = getRelevance( s );
  if( rOld==-1 || r<rOld ){
    d_relevance[s] = r;
    if( s.getKind()==FORALL ){
      for( int i=0; i<(int)d_syms[s].size(); i++ ){
        setRelevance( d_syms[s][i], r );
      }
    }else{
      for( int i=0; i<(int)d_syms_quants[s].size(); i++ ){
        setRelevance( d_syms_quants[s][i], r+1 );
      }
    }
  }
}
