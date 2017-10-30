/*********************                                                        */
/*! \file equality_query.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities used for querying about equality information
 **/

#include "theory/quantifiers/equality_query.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/equality_infer.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

EqualityQueryQuantifiersEngine::EqualityQueryQuantifiersEngine( context::Context* c, QuantifiersEngine* qe ) : d_qe( qe ), d_eqi_counter( c ), d_reset_count( 0 ){

}

EqualityQueryQuantifiersEngine::~EqualityQueryQuantifiersEngine(){
}

bool EqualityQueryQuantifiersEngine::reset( Theory::Effort e ){
  d_int_rep.clear();
  d_reset_count++;
  return processInferences( e );
}

bool EqualityQueryQuantifiersEngine::processInferences( Theory::Effort e ) {
  if( options::inferArithTriggerEq() ){
    eq::EqualityEngine* ee = getEngine();
    //updated implementation
    EqualityInference * ei = d_qe->getEqualityInference();
    while( d_eqi_counter.get()<ei->getNumPendingMerges() ){
      Node eq = ei->getPendingMerge( d_eqi_counter.get() );
      Node eq_exp = ei->getPendingMergeExplanation( d_eqi_counter.get() );
      Trace("quant-engine-ee-proc") << "processInferences : Infer : " << eq << std::endl;
      Trace("quant-engine-ee-proc") << "      explanation : " << eq_exp << std::endl;
      Assert( ee->hasTerm( eq[0] ) );
      Assert( ee->hasTerm( eq[1] ) );
      if( areDisequal( eq[0], eq[1] ) ){
        Trace("quant-engine-ee-proc") << "processInferences : Conflict : " << eq << std::endl;
        if( Trace.isOn("term-db-lemma") ){
          Trace("term-db-lemma") << "Disequal terms, equal by normalization : " << eq[0] << " " << eq[1] << "!!!!" << std::endl;
          if( !d_qe->getTheoryEngine()->needCheck() ){
            Trace("term-db-lemma") << "  all theories passed with no lemmas." << std::endl;
            //this should really never happen (implies arithmetic is incomplete when sharing is enabled)
            Assert( false );
          }
          Trace("term-db-lemma") << "  add split on : " << eq << std::endl;
        }
        d_qe->addSplit( eq );
        return false;
      }else{
        ee->assertEquality( eq, true, eq_exp );
        d_eqi_counter = d_eqi_counter.get() + 1;
      }
    }
    Assert( ee->consistent() );
  }
  return true;
}

bool EqualityQueryQuantifiersEngine::hasTerm( Node a ){
  return getEngine()->hasTerm( a );
}

Node EqualityQueryQuantifiersEngine::getRepresentative( Node a ){
  eq::EqualityEngine* ee = getEngine();
  if( ee->hasTerm( a ) ){
    return ee->getRepresentative( a );
  }else{
    return a;
  }
}

bool EqualityQueryQuantifiersEngine::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      return ee->areEqual( a, b );
    }else{
      return false;
    }
  }
}

bool EqualityQueryQuantifiersEngine::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      return ee->areDisequal( a, b, false );
    }else{
      return a.isConst() && b.isConst();
    }
  }
}

Node EqualityQueryQuantifiersEngine::getInternalRepresentative(Node a,
                                                               Node q,
                                                               int index)
{
  Assert(q.isNull() || q.getKind() == FORALL);
  Node r = getRepresentative( a );
  if( options::finiteModelFind() ){
    if( r.isConst() && quantifiers::TermUtil::containsUninterpretedConstant( r ) ){
      //map back from values assigned by model, if any
      if( d_qe->getModel() ){
        Node tr = d_qe->getModel()->getRepSet()->getTermForRepresentative(r);
        if (!tr.isNull())
        {
          r = tr;
          r = getRepresentative( r );
        }else{
          if( r.getType().isSort() ){
            Trace("internal-rep-warn") << "No representative for UF constant." << std::endl;
            //should never happen : UF constants should never escape model
            Assert( false );
          }
        }
      }
    }
  }
  if( options::quantRepMode()==quantifiers::QUANT_REP_MODE_EE ){
    return r;
  }else{
    TypeNode v_tn = q.isNull() ? a.getType() : q[0][index].getType();
    std::map<Node, Node>& v_int_rep = d_int_rep[v_tn];
    std::map<Node, Node>::const_iterator itir = v_int_rep.find(r);
    if (itir != v_int_rep.end())
    {
      return itir->second;
    }
    else
    {
      //find best selection for representative
      Node r_best;
      // if( options::fmfRelevantDomain() && !q.isNull() ){
      //  Trace("internal-rep-debug") << "Consult relevant domain to mkRep " <<
      //  r << std::endl;
      //  r_best = d_qe->getRelevantDomain()->getRelevantTerm( q, index, r );
      //  Trace("internal-rep-debug") << "Returned " << r_best << " " << r <<
      //  std::endl;
      //}
      std::vector< Node > eqc;
      getEquivalenceClass( r, eqc );
      Trace("internal-rep-select") << "Choose representative for equivalence class : { ";
      for( unsigned i=0; i<eqc.size(); i++ ){
        if (i > 0)
        {
          Trace("internal-rep-select") << ", ";
        }
        Trace("internal-rep-select") << eqc[i];
      }
      Trace("internal-rep-select")  << " }, type = " << v_tn << std::endl;
      int r_best_score = -1;
      for( size_t i=0; i<eqc.size(); i++ ){
        int score = getRepScore(eqc[i], q, index, v_tn);
        if( score!=-2 ){
          if( r_best.isNull() || ( score>=0 && ( r_best_score<0 || score<r_best_score ) ) ){
            r_best = eqc[i];
            r_best_score = score;
          }
        }
      }
      if( r_best.isNull() ){
        Trace("internal-rep-warn") << "No valid choice for representative in eqc class." << std::endl;
        r_best = r;
      }
      //now, make sure that no other member of the class is an instance
      std::unordered_map<TNode, Node, TNodeHashFunction> cache;
      r_best = getInstance( r_best, eqc, cache );
      //store that this representative was chosen at this point
      if( d_rep_score.find( r_best )==d_rep_score.end() ){
        d_rep_score[ r_best ] = d_reset_count;
      }
      Trace("internal-rep-select") << "...Choose " << r_best << " with score " << r_best_score << std::endl;
      Assert( r_best.getType().isSubtypeOf( v_tn ) );
      v_int_rep[r] = r_best;
      if( r_best!=a ){
        Trace("internal-rep-debug") << "rep( " << a << " ) = " << r << ", " << std::endl;
        Trace("internal-rep-debug") << "int_rep( " << a << " ) = " << r_best << ", " << std::endl;
      }
      return r_best;
    }
  }
}

void EqualityQueryQuantifiersEngine::flattenRepresentatives( std::map< TypeNode, std::vector< Node > >& reps ) {
  //make sure internal representatives currently exist
  for( std::map< TypeNode, std::vector< Node > >::iterator it = reps.begin(); it != reps.end(); ++it ){
    if( it->first.isSort() ){
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node r = getInternalRepresentative( it->second[i], Node::null(), 0 );
      }
    }
  }
  Trace("internal-rep-flatten") << "---Flattening representatives : " << std::endl;
  for( std::map< TypeNode, std::map< Node, Node > >::iterator itt = d_int_rep.begin(); itt != d_int_rep.end(); ++itt ){
    for( std::map< Node, Node >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
      Trace("internal-rep-flatten") << itt->first << " : irep( " << it->first << " ) = " << it->second << std::endl;
    }
  }
  //store representatives for newly created terms
  std::map< Node, Node > temp_rep_map;

  bool success;
  do {
    success = false;
    for( std::map< TypeNode, std::map< Node, Node > >::iterator itt = d_int_rep.begin(); itt != d_int_rep.end(); ++itt ){
      for( std::map< Node, Node >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
        if( it->second.getKind()==APPLY_UF && it->second.getType().isSort() ){
          Node ni = it->second;
          std::vector< Node > cc;
          cc.push_back( it->second.getOperator() );
          bool changed = false;
          for( unsigned j=0; j<ni.getNumChildren(); j++ ){
            if( ni[j].getType().isSort() ){
              Node r = getRepresentative( ni[j] );
              if( itt->second.find( r )==itt->second.end() ){
                Assert( temp_rep_map.find( r )!=temp_rep_map.end() );
                r = temp_rep_map[r];
              }
              if( r==ni ){
                //found sub-term as instance
                Trace("internal-rep-flatten-debug") << "...Changed " << it->second << " to subterm " << ni[j] << std::endl;
                itt->second[it->first] = ni[j];
                changed = false;
                success = true;
                break;
              }else{
                Node ir = itt->second[r];
                cc.push_back( ir );
                if( ni[j]!=ir ){
                  changed = true;
                }
              }
            }else{
              changed = false;
              break;
            }
          }
          if( changed ){
            Node n = NodeManager::currentNM()->mkNode( APPLY_UF, cc );
            Trace("internal-rep-flatten-debug") << "...Changed " << it->second << " to " << n << std::endl;
            success = true;
            itt->second[it->first] = n;
            temp_rep_map[n] = it->first;
          }
        }
      }
    }
  }while( success );
  Trace("internal-rep-flatten") << "---After flattening : " << std::endl;
  for( std::map< TypeNode, std::map< Node, Node > >::iterator itt = d_int_rep.begin(); itt != d_int_rep.end(); ++itt ){
    for( std::map< Node, Node >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
      Trace("internal-rep-flatten") << itt->first << " : irep( " << it->first << " ) = " << it->second << std::endl;
    }
  }
}

eq::EqualityEngine* EqualityQueryQuantifiersEngine::getEngine(){
  return d_qe->getActiveEqualityEngine();
}

void EqualityQueryQuantifiersEngine::getEquivalenceClass( Node a, std::vector< Node >& eqc ){
  eq::EqualityEngine* ee = getEngine();
  if( ee->hasTerm( a ) ){
    Node rep = ee->getRepresentative( a );
    eq::EqClassIterator eqc_iter( rep, ee );
    while( !eqc_iter.isFinished() ){
      eqc.push_back( *eqc_iter );
      eqc_iter++;
    }
  }else{
    eqc.push_back( a );
  }
  //a should be in its equivalence class
  Assert( std::find( eqc.begin(), eqc.end(), a )!=eqc.end() );
}

TNode EqualityQueryQuantifiersEngine::getCongruentTerm( Node f, std::vector< TNode >& args ) {
  return d_qe->getTermDatabase()->getCongruentTerm( f, args );
}

//helper functions

Node EqualityQueryQuantifiersEngine::getInstance( Node n, const std::vector< Node >& eqc, std::unordered_map<TNode, Node, TNodeHashFunction>& cache ){
  if(cache.find(n) != cache.end()) {
    return cache[n];
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    Node nn = getInstance( n[i], eqc, cache );
    if( !nn.isNull() ){
      return cache[n] = nn;
    }
  }
  if( std::find( eqc.begin(), eqc.end(), n )!=eqc.end() ){
    return cache[n] = n;
  }else{
    return cache[n] = Node::null();
  }
}

//-2 : invalid, -1 : undesired, otherwise : smaller the score, the better
int EqualityQueryQuantifiersEngine::getRepScore(Node n,
                                                Node q,
                                                int index,
                                                TypeNode v_tn)
{
  if( options::cbqi() && quantifiers::TermUtil::hasInstConstAttr(n) ){  //reject
    return -2;
  }else if( !n.getType().isSubtypeOf( v_tn ) ){  //reject if incorrect type
    return -2;
  }else if( options::lteRestrictInstClosure() && ( !d_qe->getTermDatabase()->isInstClosure( n ) || !d_qe->getTermDatabase()->hasTermCurrent( n, false ) ) ){
    return -1;
  }else if( options::instMaxLevel()!=-1 ){
    //score prefer lowest instantiation level
    if( n.hasAttribute(InstLevelAttribute()) ){
      return n.getAttribute(InstLevelAttribute());
    }else{
      return options::instLevelInputOnly() ? -1 : 0;
    }
  }else{
    if( options::quantRepMode()==quantifiers::QUANT_REP_MODE_FIRST ){
      //score prefers earliest use of this term as a representative
      return d_rep_score.find( n )==d_rep_score.end() ? -1 : d_rep_score[n];
    }else{
      Assert( options::quantRepMode()==quantifiers::QUANT_REP_MODE_DEPTH );
      return quantifiers::TermUtil::getTermDepth( n );
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
