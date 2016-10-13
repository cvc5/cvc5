/*********************                                                        */
/*! \file inst_propagator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** Propagate mechanism for instantiations
 **/

#include <vector>

#include "theory/quantifiers/inst_propagator.h"
#include "theory/rewriter.h"
#include "theory/quantifiers/term_database.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;


EqualityQueryInstProp::EqualityQueryInstProp( QuantifiersEngine* qe ) : d_qe( qe ){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

bool EqualityQueryInstProp::reset( Theory::Effort e ) {
  d_uf.clear();
  d_uf_exp.clear();
  d_diseq_list.clear();
  d_uf_func_map_trie.clear();
  return true;
}

/** contains term */
bool EqualityQueryInstProp::hasTerm( Node a ) {
  if( getEngine()->hasTerm( a ) ){
    return true;
  }else{
    std::vector< Node > exp;
    Node ar = getUfRepresentative( a, exp );
    return !ar.isNull() && getEngine()->hasTerm( ar );
  }
}

/** get the representative of the equivalence class of a */
Node EqualityQueryInstProp::getRepresentative( Node a ) {
  if( getEngine()->hasTerm( a ) ){
    a = getEngine()->getRepresentative( a );
  }
  std::vector< Node > exp;
  Node ar = getUfRepresentative( a, exp );
  return ar.isNull() ? a : ar;
}

/** returns true if a and b are equal in the current context */
bool EqualityQueryInstProp::areEqual( Node a, Node b ) {
  if( a==b ){
    return true;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      if( ee->areEqual( a, b ) ){
        return true;
      }
    }
    return false;
  }
}

/** returns true is a and b are disequal in the current context */
bool EqualityQueryInstProp::areDisequal( Node a, Node b ) {
  if( a==b ){
    return false;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      if( ee->areDisequal( a, b, false ) ){
        return true;
      }
    }
    return false;
  }
}

/** get the equality engine associated with this query */
eq::EqualityEngine* EqualityQueryInstProp::getEngine() {
  return d_qe->getMasterEqualityEngine();
}

/** get the equivalence class of a */
void EqualityQueryInstProp::getEquivalenceClass( Node a, std::vector< Node >& eqc ) {
  //TODO?
}

TNode EqualityQueryInstProp::getCongruentTerm( Node f, std::vector< TNode >& args ) {
  TNode t = d_qe->getTermDatabase()->getCongruentTerm( f, args );
  if( !t.isNull() ){
    return t;
  }else{
    return d_uf_func_map_trie[f].existsTerm( args );
  }
}

Node EqualityQueryInstProp::getRepresentativeExp( Node a, std::vector< Node >& exp ) {
  bool engine_has_a = getEngine()->hasTerm( a );
  if( engine_has_a ){
    a = getEngine()->getRepresentative( a );
  }
  //get union find representative, if this occurs in the equality engine, return it
  unsigned prev_size = exp.size();
  Node ar = getUfRepresentative( a, exp );
  if( !ar.isNull() ){
    if( engine_has_a || getEngine()->hasTerm( ar ) ){
      Trace("qip-eq") << "getRepresentativeExp " << a << " returns " << ar << std::endl;
      Assert( getEngine()->hasTerm( ar ) );
      Assert( getEngine()->getRepresentative( ar )==ar );
      return ar;
    }
  }else{
    if( engine_has_a ){
      return a;
    }
  }
  //retract explanation
  while( exp.size()>prev_size ){
    exp.pop_back();
  }
  return Node::null();
}

bool EqualityQueryInstProp::areEqualExp( Node a, Node b, std::vector< Node >& exp ) {
  if( areEqual( a, b ) ){
    return true;
  }else{
    std::vector< Node > exp_a;
    Node ar = getUfRepresentative( a, exp_a );
    if( !ar.isNull() ){
      std::vector< Node > exp_b;
      if( ar==getUfRepresentative( b, exp_b ) ){
        merge_exp( exp, exp_a );
        merge_exp( exp, exp_b );
        return true;
      }
    }
    return false;
  }
}

bool EqualityQueryInstProp::areDisequalExp( Node a, Node b, std::vector< Node >& exp ) {
  if( areDisequal( a, b ) ){
    return true;
  }else{
    //Assert( getRepresentative( a )==a );
    //Assert( getRepresentative( b )==b );
    std::map< Node, std::vector< Node > >::iterator itd = d_diseq_list[a].find( b );
    if( itd!=d_diseq_list[a].end() ){
      exp.insert( exp.end(), itd->second.begin(), itd->second.end() );
      return true;
    }else{
      return false;
    }
  }
}

TNode EqualityQueryInstProp::getCongruentTermExp( Node f, std::vector< TNode >& args, std::vector< Node >& exp ) {
  TNode t = d_qe->getTermDatabase()->getCongruentTerm( f, args );
  if( !t.isNull() ){
    return t;
  }else{
    TNode tt = d_uf_func_map_trie[f].existsTerm( args );
    if( !tt.isNull() ){
      //TODO?
      return tt;
    }else{
      return tt;
    }
  }
}

Node EqualityQueryInstProp::getUfRepresentative( Node a, std::vector< Node >& exp ) {
  Assert( exp.empty() );
  std::map< Node, Node >::iterator it = d_uf.find( a );
  if( it!=d_uf.end() ){
    if( it->second==a ){
      Assert( d_uf_exp[ a ].empty() );
      return it->second;
    }else{
      Node m = getUfRepresentative( it->second, exp );
      Assert( !m.isNull() );
      if( m!=it->second ){
        //update union find
        d_uf[ a ] = m;
        //update explanation : merge the explanation of the parent
        merge_exp( d_uf_exp[ a ], exp );
        Trace("qip-eq") << "EqualityQueryInstProp::getUfRepresentative : merge " << a << " -> " << m << ", exp size=" << d_uf_exp[ a ].size() << std::endl;
      }
      //add current explanation to exp: note that exp is a subset of d_uf_exp[ a ], reset
      exp.clear();
      exp.insert( exp.end(), d_uf_exp[ a ].begin(), d_uf_exp[ a ].end() );
      return m;
    }
  }else{
    return Node::null();
  }
}

// set a == b with reason, return status, modify a and b to representatives pre-merge
int EqualityQueryInstProp::setEqual( Node& a, Node& b, bool pol, std::vector< Node >& reason ) {
  if( a==b ){
    return pol ? STATUS_NONE : STATUS_CONFLICT;
  }
  int status = pol ? STATUS_MERGED_UNKNOWN : STATUS_NONE;
  Trace("qip-eq") << "EqualityQueryInstProp::setEqual " << a << ", " << b << ", pol = " << pol << ", reason size = " << reason.size() << std::endl;
  //get the representative for a
  std::vector< Node > exp_a;
  Node ar = getUfRepresentative( a, exp_a );
  if( ar.isNull() ){
    Assert( exp_a.empty() );
    ar = a;
  }
  if( ar==b ){
    Trace("qip-eq") << "EqualityQueryInstProp::setEqual : already equal" << std::endl;
    if( pol ){
      return STATUS_NONE;
    }else{
      merge_exp( reason, exp_a );
      return STATUS_CONFLICT;
    }
  }
  bool swap = false;
  //get the representative for b
  std::vector< Node > exp_b;
  Node br = getUfRepresentative( b, exp_b );
  if( br.isNull() ){
    Assert( exp_b.empty() );
    br = b;
    if( !getEngine()->hasTerm( br ) ){
      if( ar!=a || getEngine()->hasTerm( ar ) ){
        swap = true;
      }
    }else{
      if( getEngine()->hasTerm( ar ) ){
        status = STATUS_MERGED_KNOWN;
      }
    }
  }else{
    if( ar==br ){
      Trace("qip-eq") << "EqualityQueryInstProp::setEqual : already equal" << std::endl;
      if( pol ){
        return STATUS_NONE;
      }else{
        merge_exp( reason, exp_a );
        merge_exp( reason, exp_b );
        return STATUS_CONFLICT;
      }
    }else if( getEngine()->hasTerm( ar ) ){
      if( getEngine()->hasTerm( br ) ){
        status = STATUS_MERGED_KNOWN;
      }else{
        swap = true;
      }
    }
  }

  if( swap ){
    //swap
    Node temp_r = ar;
    ar = br;
    br = temp_r;
  }

  Assert( !getEngine()->hasTerm( ar ) || getEngine()->hasTerm( br ) );
  Assert( ar!=br );

  std::vector< Node > exp_d;
  if( areDisequalExp( ar, br, exp_d ) ){
    if( pol ){
      merge_exp( reason, exp_b );
      merge_exp( reason, exp_b );
      merge_exp( reason, exp_d );
      return STATUS_CONFLICT;
    }else{
      return STATUS_NONE;
    }
  }else{
    if( pol ){
      //update the union find
      Assert( d_uf_exp[ar].empty() );
      Assert( d_uf_exp[br].empty() );

      //registerUfTerm( ar );
      d_uf[ar] = br;
      merge_exp( d_uf_exp[ar], exp_a );
      merge_exp( d_uf_exp[ar], exp_b );
      merge_exp( d_uf_exp[ar], reason );

      //registerUfTerm( br );
      d_uf[br] = br;
      d_uf_exp[br].clear();

      Trace("qip-eq") << "EqualityQueryInstProp::setEqual : merge " << ar << " -> " << br << ", exp size = " << d_uf_exp[ar].size() << ", status = " << status << std::endl;
      a = ar;
      b = br;

      //carry disequality list
      std::map< Node, std::map< Node, std::vector< Node > > >::iterator itd = d_diseq_list.find( ar );
      if( itd!=d_diseq_list.end() ){
        for( std::map< Node, std::vector< Node > >::iterator itdd = itd->second.begin(); itdd != itd->second.end(); ++itdd ){
          Node d = itdd->first;
          if( d_diseq_list[br].find( d )==d_diseq_list[br].end() ){
            merge_exp( d_diseq_list[br][d], itdd->second );
            merge_exp( d_diseq_list[br][d], d_uf_exp[ar] );
          }
        }
      }

      return status;
    }else{
      Trace("qip-eq") << "EqualityQueryInstProp::setEqual : disequal " << ar << " <> " << br << std::endl;
      Assert( d_diseq_list[ar].find( br )==d_diseq_list[ar].end() );
      Assert( d_diseq_list[br].find( ar )==d_diseq_list[br].end() );

      merge_exp( d_diseq_list[ar][br], reason );
      merge_exp( d_diseq_list[br][ar], reason );
      return STATUS_NONE;
    }
  }
}

void EqualityQueryInstProp::registerUfTerm( TNode n ) {
  if( d_uf.find( n )==d_uf.end() ){
    if( !getEngine()->hasTerm( n ) ){
      TNode f = d_qe->getTermDatabase()->getMatchOperator( n );
      if( !f.isNull() ){
        std::vector< TNode > args;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          if( !getEngine()->hasTerm( n[i] ) ){
            return;
          }else{
            args.push_back( n[i] );
          }
        }
        d_uf_func_map_trie[f].addTerm( n, args );
      }
    }
  }
}

//void EqualityQueryInstProp::addArgument( std::vector< Node >& args, std::vector< Node >& props, Node n, bool is_prop, bool pol ) {
void EqualityQueryInstProp::addArgument( Node n, std::vector< Node >& args, std::vector< Node >& watch, bool is_watch ) {
  if( is_watch ){
    watch.push_back( n );
  }
  args.push_back( n );
}

bool EqualityQueryInstProp::isPropagateLiteral( Node n ) {
  if( n==d_true || n==d_false ){
    return false;
  }else{
    Kind ak = n.getKind()==NOT ? n[0].getKind() : n.getKind();
    Assert( ak!=NOT );
    return ak!=AND && ak!=OR && ak!=IFF && ak!=ITE;
  }
}

void EqualityQueryInstProp::setWatchList( Node n, std::vector< Node >& watch, std::map< Node, std::vector< Node > >& watch_list_out ) {
  if( watch.empty() ){
    watch.push_back( n );
  }
  for( unsigned j=0; j<watch.size(); j++ ){
    Trace("qip-eval") << "Watch : " << n << " -> " << watch[j] << std::endl;
    watch_list_out[n].push_back( watch[j] );
  }
}

void EqualityQueryInstProp::collectWatchList( Node n, std::map< Node, std::vector< Node > >& watch_list_out, std::vector< Node >& watch_list ) {
  std::map< Node, std::vector< Node > >::iterator it = watch_list_out.find( n );
  if( it!=watch_list_out.end() && std::find( watch_list.begin(), watch_list.end(), n )==watch_list.end() ){
    watch_list.push_back( n );
    for( unsigned j=0; j<it->second.size(); j++ ){
      collectWatchList( it->second[j], watch_list_out, watch_list );
    }
  }
}

//this is similar to TermDb::evaluateTerm2, but tracks more information
Node EqualityQueryInstProp::evaluateTermExp( Node n, std::vector< Node >& exp, std::map< int, std::map< Node, Node > >& visited,
                                             bool hasPol, bool pol, std::map< Node, std::vector< Node > >& watch_list_out, std::vector< Node >& props ) {
  int polIndex = hasPol ? ( pol ? 1 : -1 ) : 0;
  std::map< Node, Node >::iterator itv = visited[polIndex].find( n );
  if( itv!=visited[polIndex].end() ){
    return itv->second;
  }else{
    visited[polIndex][n] = n;
    Node ret;
    //check if it should be propagated in this context
    if( hasPol && isPropagateLiteral( n ) ){
      Assert( n.getType().isBoolean() );
      //must be Boolean
      ret = evaluateTermExp( n, exp, visited, false, pol, watch_list_out, props );
      if( isPropagateLiteral( ret ) ){
        Trace("qip-eval") << "-----> propagate : " << ret << std::endl;
        props.push_back( pol ? ret : ret.negate() );
        ret = pol ? d_true : d_false;
      }
    }else{
      Trace("qip-eval") << "evaluate term : " << n << " [" << polIndex << "]" << std::endl;
      std::vector< Node > exp_n;
      ret = getRepresentativeExp( n, exp_n );
      if( ret.isNull() ){
        //term is not known to be equal to a representative in equality engine, evaluate it
        Kind k = n.getKind();
        if( k!=FORALL ){
          TNode f = d_qe->getTermDatabase()->getMatchOperator( n );
          std::vector< Node > args;
          bool ret_set = false;
          bool childChanged = false;
          int abort_i = -1;
          //get the child entailed polarity
          Assert( n.getKind()!=IMPLIES );
          bool newHasPol, newPol;
          QuantPhaseReq::getEntailPolarity( n, 0, hasPol, pol, newHasPol, newPol );
          std::vector< Node > watch;
          //for each child
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            Node c = evaluateTermExp( n[i], exp, visited, newHasPol, newPol, watch_list_out, props );
            if( c.isNull() ){
              ret = Node::null();
              ret_set = true;
              break;
            }else if( c==d_true || c==d_false ){
              //short-circuiting
              if( k==kind::AND || k==kind::OR ){
                if( (k==kind::AND)==(c==d_false) ){
                  ret = c;
                  ret_set = true;
                  break;
                }else{
                  //redundant
                  c = Node::null();
                  childChanged = true;
                }
              }else if( k==kind::ITE && i==0 ){
                ret = evaluateTermExp( n[ c==d_true ? 1 : 2], exp, visited, hasPol, pol, watch_list_out, props );
                ret_set = true;
                break;
              }else if( k==kind::NOT ){
                ret = c==d_true ? d_false : d_true;
                ret_set = true;
                break;
              }
            }
            if( !c.isNull() ){
              childChanged = childChanged || n[i]!=c;
              bool is_watch = watch_list_out.find( c )!=watch_list_out.end();
              if( !f.isNull() && is_watch ){
                // we are done if this is an UF application and an argument is unevaluated
                addArgument( c, args, watch, is_watch );
                abort_i = i;
                break;
              }else if( k==kind::AND || k==kind::OR || k==kind::ITE || k==IFF ){
                Trace("qip-eval-debug") << "Adding argument " << c << " to " << k << ", isProp = " << newHasPol << std::endl;
                if( ( k==kind::AND || k==kind::OR  ) && c.getKind()==k ){
                  //flatten
                  for( unsigned j=0; j<c.getNumChildren(); j++ ){
                    addArgument( c[j], args, watch, is_watch );
                  }
                }else{
                  addArgument( c, args, watch, is_watch );
                }
                Trace("qip-eval-debug") << "props/args = " << props.size() << "/" << args.size() << std::endl;
                //if we are in a branching position
                if( hasPol && !newHasPol && args.size()>=2 ){
                  //we are done if at least two args are unevaluated
                  abort_i = i;
                  break;
                }
              }else{
                addArgument( c, args, watch, is_watch );
              }
            }
          }
          //add remaining children if we aborted
          if( abort_i!=-1 ){
            Trace("qip-eval-debug") << "..." << n << " aborted at " << abort_i << std::endl;
            for( int i=(abort_i+1); i<(int)n.getNumChildren(); i++ ){
              args.push_back( n[i] );
            }
          }
          //if we have not short-circuited evaluation
          if( !ret_set ){
            //if it is an indexed term, return the congruent term
            if( !f.isNull() && watch.empty() ){
              std::vector< TNode > t_args;
              for( unsigned i=0; i<args.size(); i++ ) {
                Trace("qip-eval") << "arg " << i << " : " << args[i] << std::endl;
                t_args.push_back( args[i] );
              }
              Assert( args.size()==n.getNumChildren() );
              //args contains terms known by the equality engine
              TNode nn = getCongruentTerm( f, t_args );
              Trace("qip-eval") << "  got congruent term " << nn << " for " << n << std::endl;
              if( !nn.isNull() ){
                //successfully constructed representative in EE
                Assert( exp_n.empty() );
                ret = getRepresentativeExp( nn, exp_n );
                Trace("qip-eval") << "return rep, exp size = " << exp_n.size() << std::endl;
                merge_exp( exp, exp_n );
                ret_set = true;
                Assert( !ret.isNull() );
                Assert( ret!=n );
                // we have that n == ret, check if the union find should be updated TODO?
              }else{
                watch.push_back( ret );
              }
            }
            if( !ret_set ){
              if( childChanged || args.size()!=n.getNumChildren() ){
                Trace("qip-eval") << "return rewrite" << std::endl;
                if( k==kind::AND || k==kind::OR ){
                  if( args.empty() ){
                    ret = k==kind::AND ? d_true : d_false;
                    ret_set = true;
                  }else if( args.size()==1 ){
                    //need to re-evaluate (may be new propagations)
                    ret = evaluateTermExp( args[0], exp, visited, hasPol, pol, watch_list_out, props );
                    ret_set = true;
                  }
                }else{
                  Assert( args.size()==n.getNumChildren() );
                }
                if( !ret_set ){
                  if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
                    args.insert( args.begin(), n.getOperator() );
                  }
                  ret = NodeManager::currentNM()->mkNode( k, args );
                  setWatchList( ret, watch, watch_list_out );
                  ret = Rewriter::rewrite( ret );
                  //need to re-evaluate
                  ret = evaluateTermExp( ret, exp, visited, hasPol, pol, watch_list_out, props );
                }
              }else{
                ret = n;
                setWatchList( ret, watch, watch_list_out );
              }
            }
          }
        }
      }else{
        Trace("qip-eval") << "...exists in ee, return rep, exp size = " << exp_n.size() << std::endl;
        merge_exp( exp, exp_n );
      }
    }

    Trace("qip-eval") << "evaluated term : " << n << " [" << polIndex << "], got : " << ret << ", exp size = " << exp.size() << ", watch list size = " << watch_list_out.size() << std::endl;
    visited[polIndex][n] = ret;
    return ret;
  }
}

void EqualityQueryInstProp::merge_exp( std::vector< Node >& v, std::vector< Node >& v_to_merge, int up_to_size ) {
  //TODO : optimize
  if( v.empty() ){
    Assert( up_to_size==-1 || up_to_size==(int)v_to_merge.size() );
    v.insert( v.end(), v_to_merge.begin(), v_to_merge.end() );
  }else{
    //std::vector< Node >::iterator v_end = v.end();
    up_to_size = up_to_size==-1 ? (int)v_to_merge.size() : up_to_size;
    for( int j=0; j<up_to_size; j++ ){
      if( std::find( v.begin(), v.end(), v_to_merge[j] )==v.end() ){
        v.push_back( v_to_merge[j] );
      }
    }
  }
}


void InstPropagator::InstInfo::init( Node q, Node lem, std::vector< Node >& terms, Node body ) {
  d_active = true;
  //information about the instance
  d_q = q;
  d_lem = lem;
  Assert( d_terms.empty() );
  d_terms.insert( d_terms.end(), terms.begin(), terms.end() );
  //the current lemma
  d_curr = body;
  d_curr_exp.push_back( body );
}

InstPropagator::InstPropagator( QuantifiersEngine* qe ) :
d_qe( qe ), d_notify(*this), d_qy( qe ){
  d_icount = 1;
  d_conflict = false;
}

bool InstPropagator::reset( Theory::Effort e ) {
  d_icount = 1;
  d_ii.clear();
  for( unsigned i=0; i<2; i++ ){
    d_conc_to_id[i].clear();
    d_conc_to_id[i][d_qy.d_true] = 0;
  }
  d_conflict = false;
  d_watch_list.clear();
  d_update_list.clear();
  d_relevant_inst.clear();
  d_has_relevant_inst = false;
  return d_qy.reset( e );
}

bool InstPropagator::notifyInstantiation( unsigned quant_e, Node q, Node lem, std::vector< Node >& terms, Node body ) {
  if( !d_conflict ){
    if( Trace.isOn("qip-prop") ){
      Trace("qip-prop") << "InstPropagator:: Notify instantiation " << q << " : " << std::endl;
      for( unsigned i=0; i<terms.size(); i++ ){
        Trace("qip-prop") << "  " << terms[i] << std::endl;
      }
    }
    unsigned id = allocateInstantiation( q, lem, terms, body );
    //initialize the information
    if( cacheConclusion( id, body ) ){
      Assert( d_update_list.empty() );
      d_update_list.push_back( id );
      bool firstTime = true;
      //update infos in the update list until empty
      do {
        unsigned uid = d_update_list.back();
        d_update_list.pop_back();
        if( d_ii[uid].d_active ){
          update( uid, d_ii[uid], firstTime );
        }
        firstTime = false;
      }while( !d_conflict && !d_update_list.empty() );
    }else{
      d_ii[id].d_active = false;
      Trace("qip-prop") << "...duplicate." << std::endl;
    }
    Trace("qip-prop") << "...finished notify instantiation." << std::endl;
    return !d_conflict;
  }else{
    Assert( false );
    return false;
  }
}

void InstPropagator::filterInstantiations() {
  if( d_has_relevant_inst ){
    //now, inform quantifiers engine which instances should be retracted
    Trace("qip-prop-debug") << "...remove instantiation ids : ";
    for( std::map< unsigned, InstInfo >::iterator it = d_ii.begin(); it != d_ii.end(); ++it ){
      if( !it->second.d_q.isNull() ){
        if( d_relevant_inst.find( it->first )==d_relevant_inst.end() ){
          if( !d_qe->removeInstantiation( it->second.d_q, it->second.d_lem, it->second.d_terms ) ){
            Trace("qip-warn") << "WARNING : did not remove instantiation id " << it->first << std::endl;
            Assert( false );
          }else{
            Trace("qip-prop-debug") << it->first << " ";
          }
        }else{
          //mark the quantified formula as relevant
          d_qe->markRelevant( it->second.d_q );
        }
      }
    }
    Trace("qip-prop-debug") << std::endl;
    Trace("quant-engine-conflict") << "-----> InstPropagator::" << ( d_conflict ? "conflict" : "propagate" ) << " with " << d_relevant_inst.size() << " instances." << std::endl;
  }
}

unsigned InstPropagator::allocateInstantiation( Node q, Node lem, std::vector< Node >& terms, Node body ) {
  unsigned id = d_icount;
  d_icount++;
  Trace("qip-prop") << "...assign id=" << id << std::endl;
  d_ii[id].init( q, lem, terms, body );
  return id;
}

bool InstPropagator::update( unsigned id, InstInfo& ii, bool firstTime ) {
  Assert( !d_conflict );
  Assert( ii.d_active );
  Trace("qip-prop-debug") << "Update info [" << id << "]..." << std::endl;
  //update the evaluation of the current lemma
  std::map< Node, std::vector< Node > > watch_list_out;
  std::map< int, std::map< Node, Node > > visited;
  std::vector< Node > exp;
  std::vector< Node > props;
  Node eval = d_qy.evaluateTermExp( ii.d_curr, exp, visited, true, true, watch_list_out, props );
  EqualityQueryInstProp::merge_exp( ii.d_curr_exp, exp );
  if( eval.isNull() ){
    ii.d_active = false;
  }else if( firstTime || eval!=ii.d_curr ){
    std::vector< Node > watch_list;
    d_qy.collectWatchList( eval, watch_list_out, watch_list );
    if( Trace.isOn("qip-prop") ){
      Trace("qip-prop") << "Update info [" << id << "]..." << std::endl;
      Trace("qip-prop") << "...updated lemma " << ii.d_curr << " -> " << eval << std::endl; 
      Trace("qip-prop") << "...explanation = ";
      debugPrintExplanation( ii.d_curr_exp, "qip-prop" );
      Trace("qip-prop") << std::endl;
      Trace("qip-prop") << "...watch list: " << std::endl;
      for( unsigned i=0; i<watch_list.size(); i++ ){
        Trace("qip-prop") << "  " << watch_list[i] << std::endl;
      }
      Trace("qip-prop") << "...new propagations: " << std::endl;
      for( unsigned i=0; i<props.size(); i++ ){
        Trace("qip-prop") << "  " << props[i] << std::endl;
      }
      Trace("qip-prop") << std::endl;
    }
    //determine the status of eval
    if( eval==d_qy.d_false ){
      Assert( props.empty() );
      //we have inferred a conflict
      conflict( ii.d_curr_exp );
      return false;
    }else{
      for( unsigned i=0; i<props.size(); i++ ){
        Trace("qip-prop-debug2")  << "Process propagation " << props[i] << std::endl;
        Assert( d_qy.isPropagateLiteral( props[i] ) );
        //if we haven't propagated this literal yet
        if( cacheConclusion( id, props[i], 1 ) ){
          //watch list for propagated literal: may not yet be purely EE representatives
          std::vector< Node > prop_watch_list;
          d_qy.collectWatchList( props[i], watch_list_out, prop_watch_list );
        
          Node lit = props[i].getKind()==NOT ? props[i][0] : props[i];
          bool pol = props[i].getKind()!=NOT;
          if( lit.getKind()==EQUAL ){
            propagate( lit[0], lit[1], pol, ii.d_curr_exp );
          }else{
            propagate( lit, pol ? d_qy.d_true : d_qy.d_false, true, ii.d_curr_exp );
          }
          if( d_conflict ){
            return false;
          }
        }
        Trace("qip-prop-debug2")  << "Done process propagation " << props[i] << std::endl;
      }
      //if we have not inferred this conclusion yet
      if( cacheConclusion( id, eval ) ){
        ii.d_curr = eval;
        //update the watch list
        Trace("qip-prop-debug") << "...updating watch list for [" << id << "], curr is " << ii.d_curr << std::endl;
        //Here, we need to be notified of enough terms such that if we are not notified, then update( id, ii ) will return no propagations.
        //  Similar to two-watched literals, but since we are taking into account UF, we need to watch all terms on a complete path of two terms.
        for( unsigned i=0; i<watch_list.size(); i++ ){
          d_watch_list[ watch_list[i] ][ id ] = true;
        }
      }else{
        Trace("qip-prop-debug") << "...conclusion " << eval << " is duplicate." << std::endl;
        ii.d_active = false;
      }
    }
  }else{
    Trace("qip-prop-debug") << "...did not update." << std::endl;
  }
  Assert( !d_conflict );
  return true;
}

void InstPropagator::propagate( Node a, Node b, bool pol, std::vector< Node >& exp ) {
  if( Trace.isOn("qip-propagate") ){
    Trace("qip-propagate") << "* Propagate " << a << ( pol ? " == " : " != " ) << b << ", exp = ";
    debugPrintExplanation( exp, "qip-propagate" );
    Trace("qip-propagate") << "..." << std::endl;
  }
  //set equal
  int status = d_qy.setEqual( a, b, pol, exp );
  if( status==EqualityQueryInstProp::STATUS_NONE ){
    Trace("qip-prop-debug") << "...already equal/no conflict." << std::endl;
    return;
  }else if( status==EqualityQueryInstProp::STATUS_CONFLICT ){
    Trace("qip-prop-debug") << "...conflict." << std::endl;
    conflict( exp );
    return;
  }
  if( pol ){
    if( status==EqualityQueryInstProp::STATUS_MERGED_KNOWN ){
      Trace("qip-rlv-propagate") << "Relevant propagation : " << a << ( pol ? " == " : " != " ) << b << std::endl;
      Assert( d_qy.getEngine()->hasTerm( a ) );
      Assert( d_qy.getEngine()->hasTerm( b ) );
      Trace("qip-prop-debug") << "...equality between known terms." << std::endl;
      addRelevantInstances( exp, "qip-propagate" );
      //d_has_relevant_inst = true;
    }
    Trace("qip-prop-debug") << "...merged representatives " << a << " and " << b << std::endl;
    for( unsigned i=0; i<2; i++ ){
      //update terms from watched lists
      Node c = i==0 ? a : b;
      std::map< Node, std::map< unsigned, bool > >::iterator it = d_watch_list.find( c );
      if( it!=d_watch_list.end() ){
        Trace("qip-prop-debug") << "...update ids from watch list of " << c << ", size=" << it->second.size() << "..." << std::endl;
        for( std::map< unsigned, bool >::iterator itw = it->second.begin(); itw != it->second.end(); ++itw ){
          unsigned idw = itw->first;
          if( std::find( d_update_list.begin(), d_update_list.end(), idw )==d_update_list.end() ){
            Trace("qip-prop-debug") << "...will update " << idw << std::endl;
            d_update_list.push_back( idw );
          }
        }
        d_watch_list.erase( c );
      }
    }
  }
}

void InstPropagator::conflict( std::vector< Node >& exp ) {
  Trace("qip-propagate") << "Conflict, exp size =" << exp.size() << std::endl;
  d_conflict = true;
  d_relevant_inst.clear();
  addRelevantInstances( exp, "qip-propagate" );
  d_has_relevant_inst = true;
}

bool InstPropagator::cacheConclusion( unsigned id, Node body, int prop_index ) {
  Assert( prop_index==0 || prop_index==1 );
  //check if the conclusion is non-redundant
  if( d_conc_to_id[prop_index].find( body )==d_conc_to_id[prop_index].end() ){
    d_conc_to_id[prop_index][body] = id;
    return true;
  }else{
    return false;
  }
}

void InstPropagator::addRelevantInstances( std::vector< Node >& exp, const char * c ) {
  for( unsigned i=0; i<exp.size(); i++ ){
    Assert( d_conc_to_id[0].find( exp[i] )!=d_conc_to_id[0].end() );
    Trace(c) << "  relevant instance id : " << d_conc_to_id[0][ exp[i] ] << std::endl;
    d_relevant_inst[ d_conc_to_id[0][ exp[i] ] ] = true;
  }
}

void InstPropagator::debugPrintExplanation( std::vector< Node >& exp, const char * c ) {
  for( unsigned i=0; i<exp.size(); i++ ){
    Assert( d_conc_to_id[0].find( exp[i] )!=d_conc_to_id[0].end() );
    Trace(c) << d_conc_to_id[0][ exp[i] ] << " ";
  }
}

