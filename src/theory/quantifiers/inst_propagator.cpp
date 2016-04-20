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
    //TODO?
    return TNode::null();
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

      d_uf[ar] = br;
      merge_exp( d_uf_exp[ar], exp_a );
      merge_exp( d_uf_exp[ar], exp_b );
      merge_exp( d_uf_exp[ar], reason );

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

void EqualityQueryInstProp::addArgument( std::vector< Node >& args, std::vector< Node >& props, Node n, bool is_prop, bool pol ) {
  if( is_prop ){
    if( isLiteral( n ) ){
      props.push_back( pol ? n : n.negate() );
      return;
    }
  }
  args.push_back( n );
}

bool EqualityQueryInstProp::isLiteral( Node n ) {
  Kind ak = n.getKind()==NOT ? n[0].getKind() : n.getKind();
  Assert( ak!=NOT );
  return ak!=AND && ak!=OR && ak!=IFF && ak!=ITE;
}

//this is identical to TermDb::evaluateTerm2, but tracks more information
Node EqualityQueryInstProp::evaluateTermExp( Node n, std::vector< Node >& exp, std::map< Node, Node >& visited, bool hasPol, bool pol,
                                             std::map< Node, bool >& watch_list_out, std::vector< Node >& props ) {
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv != visited.end() ){
    return itv->second;
  }else{
    visited[n] = n;
    Trace("qip-eval") << "evaluate term : " << n << std::endl;
    std::vector< Node > exp_n;
    Node ret = getRepresentativeExp( n, exp_n );
    if( ret.isNull() ){
      //term is not known to be equal to a representative in equality engine, evaluate it
      Kind k = n.getKind();
      if( k==FORALL ){
        ret = Node::null();
      }else{
        std::map< Node, bool > watch_list_out_curr;
        TNode f = d_qe->getTermDatabase()->getMatchOperator( n );
        std::vector< Node > args;
        bool ret_set = false;
        bool childChanged = false;
        int abort_i = -1;
        //get the child entailed polarity
        Assert( n.getKind()!=IMPLIES );
        bool newHasPol, newPol;
        QuantPhaseReq::getEntailPolarity( n, 0, hasPol, pol, newHasPol, newPol );
        //for each child
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node c = evaluateTermExp( n[i], exp, visited, newHasPol, newPol, watch_list_out_curr, props );
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
              Assert( watch_list_out_curr.empty() );
              ret = evaluateTermExp( n[ c==d_true ? 1 : 2], exp, visited, hasPol, pol, watch_list_out_curr, props );
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
            if( !f.isNull() && !watch_list_out_curr.empty() ){
              // we are done if this is an UF application and an argument is unevaluated
              args.push_back( c );
              abort_i = i;
              break;
            }else if( ( k==kind::AND || k==kind::OR ) ){
              if( c.getKind()==k ){
                //flatten
                for( unsigned j=0; j<c.getNumChildren(); j++ ){
                  addArgument( args, props, c[j], newHasPol, newPol );
                }
              }else{
                addArgument( args, props, c, newHasPol, newPol );
              }
              //if we are in a branching position
              if( hasPol && !newHasPol && args.size()>=2 ){
                //we are done if at least two args are unevaluated
                abort_i = i;
                break;
              }
            }else if( k==kind::ITE ){
              //we are done if we are ITE and condition is unevaluated
              Assert( i==0 );
              args.push_back( c );
              abort_i = i;
              break;
            }else{
              args.push_back( c );
            }
          }
        }
        //add remaining children if we aborted
        if( abort_i!=-1 ){
          for( int i=(abort_i+1); i<(int)n.getNumChildren(); i++ ){
            args.push_back( n[i] );
          }
        }
        //copy over the watch list
        for( std::map< Node, bool >::iterator itc = watch_list_out_curr.begin(); itc != watch_list_out_curr.end(); ++itc ){
          watch_list_out[itc->first] = itc->second;
        }

        //if we have not short-circuited evaluation
        if( !ret_set ){
          //if it is an indexed term, return the congruent term
          if( !f.isNull() && watch_list_out.empty() ){
            std::vector< TNode > t_args;
            for( unsigned i=0; i<args.size(); i++ ) {
              t_args.push_back( args[i] );
            }
            Assert( args.size()==n.getNumChildren() );
            //args contains terms known by the equality engine
            TNode nn = getCongruentTerm( f, t_args );
            Trace("qip-eval") << "  got congruent term " << nn << " from DB for " << n << std::endl;
            if( !nn.isNull() ){
              //successfully constructed representative in EE
              Assert( exp_n.empty() );
              ret = getRepresentativeExp( nn, exp_n );
              Trace("qip-eval") << "return rep, exp size = " << exp_n.size() << std::endl;
              merge_exp( exp, exp_n );
              ret_set = true;
              Assert( !ret.isNull() );
            }
          }
          if( !ret_set ){
            if( childChanged ){
              Trace("qip-eval") << "return rewrite" << std::endl;
              if( ( k==kind::AND || k==kind::OR ) ){
                if( args.empty() ){
                  ret = k==kind::AND ? d_true : d_false;
                  ret_set = true;
                }else if( args.size()==1 ){
                  ret = args[0];
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
                ret = Rewriter::rewrite( ret );
                //re-evaluate
                Node ret_eval = getRepresentativeExp( ret, exp_n );
                if( !ret_eval.isNull() ){
                  ret = ret_eval;
                  watch_list_out.clear();
                }else{            
                  watch_list_out[ret] = true;
                }
              }
            }else{
              ret = n;
              watch_list_out[ret] = true;
            }
          }
        }
      }
    }else{
      Trace("qip-eval") << "...exists in ee, return rep, exp size = " << exp_n.size() << std::endl;
      merge_exp( exp, exp_n );
    }
    Trace("qip-eval") << "evaluated term : " << n << ", got : " << ret << ", exp size = " << exp.size() << std::endl;
    visited[n] = ret;
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
    unsigned id = d_icount;
    d_icount++;
    Trace("qip-prop") << "...assign id=" << id << std::endl;
    d_ii[id].init( q, lem, terms, body );
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
    return true;
  }
}

bool InstPropagator::update( unsigned id, InstInfo& ii, bool firstTime ) {
  Assert( !d_conflict );
  Assert( ii.d_active );
  Trace("qip-prop-debug") << "Update info [" << id << "]..." << std::endl;
  //update the evaluation of the current lemma
  std::map< Node, Node > visited;
  std::map< Node, bool > watch_list;
  std::vector< Node > props;
  Node eval = d_qy.evaluateTermExp( ii.d_curr, ii.d_curr_exp, visited, true, true, watch_list, props );
  if( eval.isNull() ){
    ii.d_active = false;
  }else if( firstTime || eval!=ii.d_curr ){
    if( EqualityQueryInstProp::isLiteral( eval ) ){
      props.push_back( eval );
      eval = d_qy.d_true;
      watch_list.clear();
    }
    if( Trace.isOn("qip-prop") ){
      Trace("qip-prop") << "Update info [" << id << "]..." << std::endl;
      Trace("qip-prop") << "...updated lemma " << ii.d_curr << " -> " << eval << ", exp = ";
      debugPrintExplanation( ii.d_curr_exp, "qip-prop" );
      Trace("qip-prop") << std::endl;
      Trace("qip-prop") << "...watch list: " << std::endl;
      for( std::map< Node, bool >::iterator itw = watch_list.begin(); itw!=watch_list.end(); ++itw ){
        Trace("qip-prop") << "  " << itw->first << std::endl;
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
        //if we haven't propagated this literal yet
        if( cacheConclusion( id, props[i], 1 ) ){
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
        //Here, we need to be notified of enough terms such that if we are not notified, then update( ii ) will return no propagations.
        //  Similar to two-watched literals, but since we are in UF, we need to watch all terms on a complete path of two terms.
        for( std::map< Node, bool >::iterator itw = watch_list.begin(); itw != watch_list.end(); ++itw ){
          d_watch_list[ itw->first ][ id ] = true;
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
      Assert( d_qy.getEngine()->hasTerm( a ) );
      Assert( d_qy.getEngine()->hasTerm( b ) );
      Trace("qip-prop-debug") << "...equality between known terms." << std::endl;
      addRelevantInstances( exp, "qip-propagate" );
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

  //now, inform quantifiers engine which instances should be retracted
  Trace("qip-prop-debug") << "...remove instantiation ids : ";
  for( std::map< unsigned, InstInfo >::iterator it = d_ii.begin(); it != d_ii.end(); ++it ){
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
  Trace("qip-prop-debug") << std::endl;
  //will interupt the quantifiers engine
  Trace("quant-engine-conflict") << "-----> InstPropagator::conflict with " << exp.size() << " instances." << std::endl;
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

