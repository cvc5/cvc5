/*********************                                                        */
/*! \file symmetry_breaking.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief symmetry breaking module
 **
 **/

#include "theory/quantifiers/symmetry_breaking.h"

#include <vector>

#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace std;

namespace CVC4 {


SubsortSymmetryBreaker::SubsortSymmetryBreaker(QuantifiersEngine* qe, context::Context* c) :
d_qe(qe), d_conflict(c,false) {
  d_true =  NodeManager::currentNM()->mkConst( true );
}

eq::EqualityEngine * SubsortSymmetryBreaker::getEqualityEngine() {
  return ((uf::TheoryUF*)d_qe->getTheoryEngine()->theoryOf( theory::THEORY_UF ))->getEqualityEngine();
}

bool SubsortSymmetryBreaker::areEqual( Node n1, Node n2 ) {
  return getEqualityEngine()->hasTerm( n1 ) && getEqualityEngine()->hasTerm( n2 ) && getEqualityEngine()->areEqual( n1,n2 );
}

bool SubsortSymmetryBreaker::areDisequal( Node n1, Node n2 ) {
  return getEqualityEngine()->hasTerm( n1 ) && getEqualityEngine()->hasTerm( n2 ) && getEqualityEngine()->areDisequal( n1,n2, false );
}


Node SubsortSymmetryBreaker::getRepresentative( Node n ) {
  return getEqualityEngine()->getRepresentative( n );
}

uf::StrongSolverTheoryUF * SubsortSymmetryBreaker::getStrongSolver() {
  return ((uf::TheoryUF*)d_qe->getTheoryEngine()->theoryOf( theory::THEORY_UF ))->getStrongSolver();
}

SubsortSymmetryBreaker::TypeInfo::TypeInfo( context::Context * c ) :
d_max_dom_const_sort(c,0), d_has_dom_const_sort(c,false) {
}

SubsortSymmetryBreaker::SubSortInfo::SubSortInfo( context::Context * c ) :
d_dom_constants( c ), d_first_active( c, 0 ){
  d_dc_nodes = 0;
}

unsigned SubsortSymmetryBreaker::SubSortInfo::getNumDomainConstants() {
  if( d_nodes.empty() ){
    return 0;
  }else{
    return 1 + d_dom_constants.size();
  }
}

Node SubsortSymmetryBreaker::SubSortInfo::getDomainConstant( int i ) {
  if( i==0 ){
    return d_nodes[0];
  }else{
    Assert( i<=(int)d_dom_constants.size() );
    return d_dom_constants[i-1];
  }
}

Node SubsortSymmetryBreaker::SubSortInfo::getFirstActive(eq::EqualityEngine * ee) {
  if( d_first_active.get()<(int)d_nodes.size() ){
    Node fa = d_nodes[d_first_active.get()];
    return ee->hasTerm( fa ) ? fa : Node::null();
  }else{
    return Node::null();
  }
}

SubsortSymmetryBreaker::TypeInfo * SubsortSymmetryBreaker::getTypeInfo( TypeNode tn ) {
  if( d_t_info.find( tn )==d_t_info.end() ){
    d_t_info[tn] = new TypeInfo( d_qe->getSatContext() );
  }
  return d_t_info[tn];
}

SubsortSymmetryBreaker::SubSortInfo * SubsortSymmetryBreaker::getSubSortInfo( TypeNode tn, int sid ) {
  if( d_type_info.find( sid )==d_type_info.end() ){
    d_type_info[sid] = new SubSortInfo( d_qe->getSatContext() );
    d_sub_sorts[tn].push_back( sid );
    d_sid_to_type[sid] = tn;
  }
  return d_type_info[sid];
}

void SubsortSymmetryBreaker::newEqClass( Node n ) {
  Trace("sym-break-temp") << "New eq class " << n << std::endl;
  if( !d_conflict ){
    TypeNode tn = n.getType();
    SortInference * si = d_qe->getTheoryEngine()->getSortInference();
    if( si->isWellSorted( n ) ){
      int sid = si->getSortId( n );
      Trace("sym-break-debug") << "SSB: New eq class " << n << " : " << n.getType() << " : " << sid << std::endl;
      SubSortInfo * ti = getSubSortInfo( tn, sid );
      if( std::find( ti->d_nodes.begin(), ti->d_nodes.end(), n )==ti->d_nodes.end() ){
        if( ti->d_nodes.empty() ){
          //for first subsort, we add unit equality
          if( d_sub_sorts[tn][0]!=sid ){
            Trace("sym-break-temp") << "Do sym break unit with " << d_type_info[d_sub_sorts[tn][0]]->getBaseConstant() << std::endl;
            //add unit symmetry breaking lemma
            Node eq = n.eqNode( d_type_info[d_sub_sorts[tn][0]]->getBaseConstant() );
            eq = Rewriter::rewrite( eq );
            d_unit_lemmas.push_back( eq );
            Trace("sym-break-lemma") << "*** SymBreak : Unit lemma (" << sid << "==" << d_sub_sorts[tn][0] << ") : " << eq << std::endl;
            d_pending_lemmas.push_back( eq );
          }
          Trace("sym-break-dc") << "* Set first domain constant : " << n << " for " << tn << " : " << sid << std::endl;
          ti->d_dc_nodes++;
        }
        ti->d_node_to_id[n] = ti->d_nodes.size();
        ti->d_nodes.push_back( n );
      }
      TypeInfo * tti = getTypeInfo( tn );
      if( !tti->d_has_dom_const_sort.get() ){
        tti->d_has_dom_const_sort.set( true );
        tti->d_max_dom_const_sort.set( sid );
      }
    }
  }
  Trace("sym-break-temp") << "Done new eq class" << std::endl;
}



void SubsortSymmetryBreaker::merge( Node a, Node b ) {
  if( Trace.isOn("sym-break-debug") ){
    SortInference * si = d_qe->getTheoryEngine()->getSortInference();
    int as = si->getSortId( a );
    int bs = si->getSortId( b );
    Trace("sym-break-debug") << "SSB: New merge " << a.getType() << " :: " << a << " : " << as;
    Trace("sym-break-debug") << " == " << b << " : " << bs << std::endl;
  }
}

void SubsortSymmetryBreaker::assertDisequal( Node a, Node b ) {
  if( Trace.isOn("sym-break-debug") ){
    SortInference * si = d_qe->getTheoryEngine()->getSortInference();
    int as = si->getSortId( a );
    int bs = si->getSortId( b );
    Trace("sym-break-debug") << "SSB: New assert disequal " << a.getType() << " :: " << a << " : " << as;
    Trace("sym-break-debug") << " != " << b << " : " << bs << std::endl;
  }
}

void SubsortSymmetryBreaker::processFirstActive( TypeNode tn, int sid, int curr_card ){
  SubSortInfo * ti = getSubSortInfo( tn, sid );
  if( (int)ti->getNumDomainConstants()<curr_card ){
      //static int checkCount = 0;
      //checkCount++;
      //if( checkCount%1000==0 ){
      //  std::cout << "Check count = " << checkCount << std::endl;
      //}

    Trace("sym-break-dc-debug") << "Check for domain constants " << tn << " : " << sid << ", curr_card = " << curr_card << ", ";
    Trace("sym-break-dc-debug") << "#domain constants = " << ti->getNumDomainConstants() << std::endl;
    Node fa = ti->getFirstActive(getEqualityEngine());
    bool invalid = true;
    while( invalid && !fa.isNull() && (int)ti->getNumDomainConstants()<curr_card ){
      invalid = false;
      unsigned deq = 0;
      for( unsigned i=0; i<ti->getNumDomainConstants(); i++ ){
        Node dc = ti->getDomainConstant( i );
        if( areEqual( fa, dc ) ){
          invalid = true;
          break;
        }else if( areDisequal( fa, dc ) ){
          deq++;
        }
      }
      if( deq==ti->getNumDomainConstants() ){
        Trace("sym-break-dc") << "* Can infer domain constant #" << ti->getNumDomainConstants()+1;
        Trace("sym-break-dc") << " : " << fa << " for " << tn << " : " << sid << std::endl;
        //add to domain constants
        ti->d_dom_constants.push_back( fa );
        if( ti->d_node_to_id[fa]>ti->d_dc_nodes ){
          Trace("sym-break-dc-debug") << "Swap nodes... " << ti->d_dc_nodes << " " << ti->d_node_to_id[fa] << " " << ti->d_nodes.size() << std::endl;
          //swap
          Node on = ti->d_nodes[ti->d_dc_nodes];
          int id = ti->d_node_to_id[fa];

          ti->d_nodes[ti->d_dc_nodes] = fa;
          ti->d_nodes[id] = on;
          ti->d_node_to_id[fa] = ti->d_dc_nodes;
          ti->d_node_to_id[on] = id;
        }
        ti->d_dc_nodes++;
        Trace("sym-break-dc-debug") << "Get max type info..." << std::endl;
        TypeInfo * tti = getTypeInfo( tn );
        Assert( tti->d_has_dom_const_sort.get() );
        int msid = tti->d_max_dom_const_sort.get();
        SubSortInfo * max_ti = getSubSortInfo( d_sid_to_type[msid], msid );
        Trace("sym-break-dc-debug") << "Swap nodes..." << std::endl;
        //now, check if we can apply symmetry breaking to another sort
        if( ti->getNumDomainConstants()>max_ti->getNumDomainConstants() ){
          Trace("sym-break-dc") << "Max domain constant subsort for " << tn << " becomes " << sid << std::endl;
          tti->d_max_dom_const_sort.set( sid );
        }else if( ti!=max_ti ){
          //construct symmetry breaking lemma
          //current domain constant must be disequal from all current ones
          Trace("sym-break-dc") << "Get domain constant " << ti->getNumDomainConstants()-1;
          Trace("sym-break-dc") << " from max_ti, " << max_ti->getNumDomainConstants() << std::endl;
          //apply a symmetry breaking lemma
          Node m = max_ti->getDomainConstant(ti->getNumDomainConstants()-1);
          //if fa and m are disequal from all previous domain constants in the other sort
          std::vector< Node > cc;
          for( unsigned r=0; r<2; r++ ){
            Node n = ((r==0)==(msid>sid)) ? fa : m;
            Node on = ((r==0)==(msid>sid)) ? m : fa;
            SubSortInfo * t = ((r==0)==(msid>sid)) ? max_ti : ti;
            for( unsigned i=0; i<t->d_node_to_id[on]; i++ ){
              cc.push_back( n.eqNode( t->d_nodes[i] ) );
            }
          }
          //then, we can assume fa = m
          cc.push_back( fa.eqNode( m ) );
          Node lem = NodeManager::currentNM()->mkNode( kind::OR, cc );
          lem = Rewriter::rewrite( lem );
          if( std::find( d_lemmas.begin(), d_lemmas.end(), lem )==d_lemmas.end() ){
            d_lemmas.push_back( lem );
            Trace("sym-break-lemma") << "*** Symmetry break lemma for " << tn << " (" << sid << "==" << tti->d_max_dom_const_sort.get() << ") : ";
            Trace("sym-break-lemma") << lem << std::endl;
            d_pending_lemmas.push_back( lem );
          }
        }
        invalid = true;
      }
      if( invalid ){
        ti->d_first_active.set( ti->d_first_active + 1 );
        fa = ti->getFirstActive(getEqualityEngine());
      }
    }
  }
}

void SubsortSymmetryBreaker::printDebugSubSortInfo( const char * c, TypeNode tn, int sid ) {
  Trace(c) << "SubSortInfo( " << tn << ", " << sid << " ) = " << std::endl;
  Trace(c) << "  Domain constants : ";
  SubSortInfo * ti = getSubSortInfo( tn, sid );
  for( NodeList::const_iterator it = ti->d_dom_constants.begin(); it != ti->d_dom_constants.end(); ++it ){
    Node dc = *it;
    Trace(c) << dc << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "  First active node : " << ti->getFirstActive(getEqualityEngine()) << std::endl;
}

bool SubsortSymmetryBreaker::check( Theory::Effort level ) {

  Trace("sym-break-debug") << "SymBreak : check " << level << std::endl;
  /*
  while( d_fact_index.get()<d_fact_list.size() ){
    Node f = d_fact_list[d_fact_index.get()];
    d_fact_index.set( d_fact_index.get() + 1 );
    if( f.getKind()==EQUAL ){
      merge( f[0], f[1] );
    }else if( f.getKind()==NOT && f[0].getKind()==EQUAL ){
      assertDisequal( f[0][0], f[0][1] );
    }else{
      newEqClass( f );
    }
  }
  */
  Trace("sym-break-debug") << "SymBreak : update first actives" << std::endl;
  for( std::map< TypeNode, std::vector< int > >::iterator it = d_sub_sorts.begin(); it != d_sub_sorts.end(); ++it ){
    int card = getStrongSolver()->getCardinality( it->first );
    for( unsigned i=0; i<it->second.size(); i++ ){
      //check if the first active is disequal from all domain constants
      processFirstActive( it->first, it->second[i], card );
    }
  }


  Trace("sym-break-debug") << "SymBreak : finished check, now flush lemmas... (#lemmas = " << d_pending_lemmas.size() << ")" << std::endl;
  //flush pending lemmas
  if( !d_pending_lemmas.empty() ){
    for( unsigned i=0; i<d_pending_lemmas.size(); i++ ){
      getStrongSolver()->getOutputChannel().lemma( d_pending_lemmas[i], false, true );
      ++( getStrongSolver()->d_statistics.d_sym_break_lemmas );
    }
    d_pending_lemmas.clear();
    return true;
  }else{
    return false;
  }
}



}

