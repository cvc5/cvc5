/*********************                                                        */
/*! \file theory_sets_private.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "theory/sets/cardinality_extension.h"

#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/theory_sets_private.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

CardinalityExtension::CardinalityExtension(TheorySetsPrivate& p,
                       SetsState& s,
                 eq::EqualityEngine* e,
                                     context::Context* c,
                                     context::UserContext* u)
    : d_parent(p),
    d_state(s),
      d_card_processed(u)
{
  d_zero = NodeManager::currentNM()->mkConst( Rational(0) );

  e->addFunctionKind(CARD);
}
void CardinalityExtension::check()
{
  
}

void CardinalityExtension::checkCardBuildGraph( std::vector< Node >& lemmas ) {
  Trace("sets") << "Cardinality graph..." << std::endl;
  NodeManager * nm = NodeManager::currentNM();
  //first, ensure cardinality relationships are added as lemmas for all non-basic set terms
  for( const Node& eqc : d_set_eqc )
  {
    std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( eqc );
    if( itn!=d_nvar_sets.end() ){
      for( const Node& n : itn->second ){
        if( d_congruent.find( n )==d_congruent.end() ){
          //if setminus, do for intersection instead
          if( n.getKind()==SETMINUS ){
            n = Rewriter::rewrite( nm->mkNode( INTERSECTION, n[0], n[1] ) );
          }
          registerCardinalityTerm( n, lemmas );
        }
      }
    }
  }
  Trace("sets") << "Done cardinality graph" << std::endl;
}

void CardinalityExtension::registerCardinalityTerm( Node n, std::vector< Node >& lemmas ){
  TypeNode tnc = n.getType().getSetElementType();
  if (d_t_card_enabled.find(tnc) == d_t_card_enabled.end())
  {
    // if no cardinality constraints for sets of this type, we can ignore
    return;
  }
  if( d_card_processed.find( n )!=d_card_processed.end() ){
    // already processed
    return;
  }
  NodeManager * nm = NodeManager::currentNM();
  d_card_processed.insert( n );
  Trace("sets-card") << "Cardinality lemmas for " << n << " : " << std::endl;
  std::vector< Node > cterms;
  if( n.getKind()==INTERSECTION ){
    for( unsigned e=0; e<2; e++ ){
      Node s = nm->mkNode( SETMINUS, n[e], n[1-e] );
      cterms.push_back( s );
    }
    Node pos_lem = nm->mkNode( GEQ, nm->mkNode( CARD, n ), d_zero );
    // FIXME
    //assertInference( pos_lem, d_emp_exp, lemmas, "pcard", 1 );
  }else{
    cterms.push_back( n );
  }
  for( unsigned k=0, csize = cterms.size(); k<csize; k++ ){
    Node nn = cterms[k];
    Node nk = getProxy( nn );
    Node pos_lem = nm->mkNode( GEQ, nm->mkNode( CARD, nk ), d_zero );
    assertInference( pos_lem, d_emp_exp, lemmas, "pcard", 1 );
    if( nn!=nk ){
      Node lem = nm->mkNode( EQUAL, nm->mkNode( CARD, nk ),
                                                                nm->mkNode( CARD, nn ) );
      lem = Rewriter::rewrite( lem );
      Trace("sets-card") << "  " << k << " : " << lem << std::endl;
      assertInference( lem, d_emp_exp, lemmas, "card", 1 );
    }
  }
}

void CardinalityExtension::checkCardCycles( std::vector< Node >& lemmas ) {
  Trace("sets") << "Check cardinality cycles..." << std::endl;
  //build order of equivalence classes, also build cardinality graph
  std::vector< Node > set_eqc_tmp;
  // FIXME: improve
  set_eqc_tmp.insert( set_eqc_tmp.end(), d_parent.d_set_eqc.begin(), d_parent.d_set_eqc.end() );
  d_set_eqc.clear();
  d_card_parent.clear();
  for( unsigned i=0; i<set_eqc_tmp.size(); i++ ){
    std::vector< Node > curr;
    std::vector< Node > exp;
    checkCardCyclesRec( set_eqc_tmp[i], curr, exp, lemmas );
    // FIXME
    /*
    flushLemmas( lemmas );
    if( d_parent.hasProcessed() ){
      return;
    }
    */
  }
  Trace("sets") << "Done check cardinality cycles" << std::endl;
}

void CardinalityExtension::checkCardCyclesRec( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp, std::vector< Node >& lemmas ) {
  NodeManager * nm = NodeManager::currentNM();
  if( std::find( curr.begin(), curr.end(), eqc )!=curr.end() ){
    Trace("sets-debug") << "Found venn region loop..." << std::endl;
    if( curr.size()>1 ){
      //all regions must be equal
      std::vector< Node > conc;
      for( unsigned i=1; i<curr.size(); i++ ){
        conc.push_back( curr[0].eqNode( curr[i] ) );
      }
      Node fact = conc.size()==1 ? conc[0] : nm->mkNode( AND, conc );
      // FIXME
      /*
      assertInference( fact, exp, lemmas, "card_cycle" );
      flushLemmas( lemmas );
      */
    }else{
      //should be guaranteed based on not exploring equal parents
      Assert( false );
    }
    return;
  }
  if( std::find( d_set_eqc.begin(), d_set_eqc.end(), eqc )!=d_set_eqc.end() ){
    // already processed
    return;
  }
  std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( eqc );
  if( itn==d_nvar_sets.end() ){
    // no non-variable sets, trivial
    d_set_eqc.push_back(eqc);
    return;
  }
  curr.push_back( eqc );
  TypeNode tn = eqc.getType();
  bool is_empty = eqc==d_eqc_emptyset[tn];
  Node emp_set = getEmptySet( tn );
  for( const Node& n : itn->second ){
    Kind nk = n.getKind();
    if( nk!=INTERSECTION && nk!=SETMINUS ){
      continue;
    }
    Trace("sets-debug") << "Build cardinality parents for " << n << "..." << std::endl;
    std::vector< Node > sib;
    unsigned true_sib = 0;
    if( n.getKind()==INTERSECTION ){
      d_card_base[n] = n;
      for( unsigned e=0; e<2; e++ ){
        Node sm = Rewriter::rewrite( nm->mkNode( SETMINUS, n[e], n[1-e] ) );
        sib.push_back( sm );
      }
      true_sib = 2;
    }else{
      Node si = Rewriter::rewrite( nm->mkNode( INTERSECTION, n[0], n[1] ) );
      sib.push_back( si );
      d_card_base[n] = si;
      Node osm = Rewriter::rewrite( nm->mkNode( SETMINUS, n[1], n[0] ) );
      sib.push_back( osm );
      true_sib = 1;
    }
    Node u = Rewriter::rewrite( nm->mkNode( UNION, n[0], n[1] ) );
    if( !d_equalityEngine.hasTerm( u ) ){
      u = Node::null();
    }
    unsigned n_parents = true_sib + ( u.isNull() ? 0 : 1 );
    //if this set is empty
    if( is_empty ){
      Assert( ee_areEqual( n, emp_set ) );
      Trace("sets-debug") << "  empty, parents equal siblings" << std::endl;
      std::vector< Node > conc;
      //parent equal siblings
      for( unsigned e=0; e<true_sib; e++ ){
        if( d_equalityEngine.hasTerm( sib[e] ) && !ee_areEqual( n[e], sib[e] ) )
        {
          conc.push_back( n[e].eqNode( sib[e] ) );
        }
      }
      assertInference( conc, n.eqNode( emp_set ), lemmas, "cg_emp" );
      flushLemmas( lemmas );
      if( d_parent.hasProcessed() ){
        return;
      }else{
        //justify why there is no edge to parents (necessary?)
        for( unsigned e=0; e<n_parents; e++ ){
          Node p = (e==true_sib) ? u : n[e];
          
        }
      }
    }else{
      std::vector< Node > card_parents;
      std::vector< int > card_parent_ids;
      //check if equal to a parent
      for( unsigned e=0; e<n_parents; e++ ){
        Trace("sets-debug") << "  check parent " << e << "/" << n_parents << std::endl;
        bool is_union = e==true_sib;
        Node p = (e==true_sib) ? u : n[e];
        Trace("sets-debug") << "  check relation to parent " << p << ", isu=" << is_union << "..." << std::endl;
        //if parent is empty
        if( ee_areEqual( p, emp_set ) ){
          Trace("sets-debug") << "  it is empty..." << std::endl;
          Assert( !ee_areEqual( n, emp_set ) );
          assertInference( n.eqNode( emp_set ), p.eqNode( emp_set ), lemmas, "cg_emppar" );
          if( d_parent.hasProcessed() ){
            return;
          }
        //if we are equal to a parent
        }else if( ee_areEqual( p, n ) ){
          Trace("sets-debug") << "  it is equal to this..." << std::endl;
          std::vector< Node > conc;
          std::vector< int > sib_emp_indices;
          if( is_union ){
            for( unsigned s=0; s<sib.size(); s++ ){
              sib_emp_indices.push_back( s );
            }
          }else{
            sib_emp_indices.push_back( e );
          }
          //sibling(s) are empty
          for( unsigned si : sib_emp_indices ){
            if( !ee_areEqual( sib[si], emp_set ) ){
              conc.push_back( sib[si].eqNode( emp_set ) );
            }else{
              Trace("sets-debug") << "Sibling " << sib[si] << " is already empty." << std::endl;
            }
          }
          if( !is_union && nk==INTERSECTION && !u.isNull() ){
            //union is equal to other parent
            if( !ee_areEqual( u, n[1-e] ) ){
              conc.push_back( u.eqNode( n[1-e] ) );
            }
          }
          Trace("sets-debug") << "...derived " << conc.size() << " conclusions" << std::endl;
          assertInference( conc, n.eqNode( p ), lemmas, "cg_eqpar" );
          flushLemmas( lemmas );
          if( d_parent.hasProcessed() ){
            return;
          }
        }else{
          Trace("sets-cdg") << "Card graph : " << n << " -> " << p << std::endl;
          //otherwise, we a syntactic subset of p
          card_parents.push_back( p );
          card_parent_ids.push_back( is_union ? 2 : e );
        }
      }
      Assert( d_card_parent[n].empty() );
      Trace("sets-debug") << "get parent representatives..." << std::endl;
      //for each parent, take their representatives
      for( unsigned k=0; k<card_parents.size(); k++ ){
        Node eqcc = d_equalityEngine.getRepresentative( card_parents[k] );
        Trace("sets-debug") << "Check card parent " << k << "/" << card_parents.size() << std::endl;
        
        //if parent is singleton, then we should either be empty to equal to it
        std::map< Node, Node >::iterator itps = d_eqc_singleton.find( eqcc );
        if( itps!=d_eqc_singleton.end() ){
          bool eq_parent = false;
          std::vector< Node > exp;
          addEqualityToExp( card_parents[k], itps->second, exp );
          if( ee_areDisequal( n, emp_set ) ){
            exp.push_back( n.eqNode( emp_set ).negate() );
            eq_parent = true;
          }else{
            std::map< Node, std::map< Node, Node > >::iterator itpm = d_pol_mems[0].find( eqc );
            if( itpm!=d_pol_mems[0].end() && !itpm->second.empty() ){
              Node pmem = itpm->second.begin()->second;
              exp.push_back( pmem );
              addEqualityToExp( n, pmem[1], exp );
              eq_parent = true;
            }
          }
          //must be equal to parent
          if( eq_parent ){
            Node conc = n.eqNode(  card_parents[k] );
            assertInference( conc, exp, lemmas, "cg_par_sing" );
            flushLemmas( lemmas );
          }else{
            //split on empty
            Trace("sets-nf") << "Split empty : " << n << std::endl;
            split( n.eqNode( emp_set ), 1 );
          }
          Assert( d_parent.hasProcessed() );
          return;
        }else{
          bool dup = false;
          for( unsigned l=0; l<d_card_parent[n].size(); l++ ){
            if( eqcc==d_card_parent[n][l] ){
              Trace("sets-debug") << "  parents " << l << " and " << k << " are equal, ids = " << card_parent_ids[l] << " " << card_parent_ids[k] << std::endl;
              dup = true;
              if( n.getKind()==INTERSECTION ){
                Assert( card_parent_ids[l]!=2 );
                std::vector< Node > conc;
                if( card_parent_ids[k]==2 ){
                  //intersection is equal to other parent
                  unsigned pid = 1-card_parent_ids[l];
                  if( !ee_areEqual( n[pid], n ) ){
                    Trace("sets-debug") << "  one of them is union, make equal to other..." << std::endl;
                    conc.push_back( n[pid].eqNode( n ) );
                  }
                }else{
                  if( !ee_areEqual( card_parents[k], n ) ){
                    Trace("sets-debug") << "  neither is union, make equal to one parent..." << std::endl;
                    //intersection is equal to one of the parents
                    conc.push_back( card_parents[k].eqNode( n ) );
                  }
                }
                assertInference( conc, card_parents[k].eqNode( d_card_parent[n][l] ), lemmas, "cg_pareq" );
                flushLemmas( lemmas );
                if( d_parent.hasProcessed() ){
                  return;
                }
              }
            }
          }
          if( !dup ){
            d_card_parent[n].push_back( eqcc );
          }
        }
      }
      //now recurse on parents (to ensure their normal will be computed after this eqc)
      exp.push_back( eqc.eqNode( n ) );
      for( unsigned k=0; k<d_card_parent[n].size(); k++ ){
        checkCardCyclesRec( d_card_parent[n][k], curr, exp, lemmas );
        if( d_parent.hasProcessed() ){
          return;
        }
      }
      exp.pop_back();
    }
  }
  curr.pop_back();
  //parents now processed, can add to ordered list
  d_set_eqc.push_back( eqc );

}

void CardinalityExtension::checkNormalForms( std::vector< Node >& lemmas, std::vector< Node >& intro_sets ){
  Trace("sets") << "Check normal forms..." << std::endl;
  // now, build normal form for each equivalence class
  //   d_set_eqc is now sorted such that for each d_set_eqc[i], d_set_eqc[j], 
  //      if d_set_eqc[i] is a strict syntactic subterm of d_set_eqc[j], then i<j.
  d_ff.clear();
  d_nf.clear();
  for( int i=(int)(d_set_eqc.size()-1); i>=0; i-- ){
    checkNormalForm( d_set_eqc[i], intro_sets );
    if( d_parent.hasProcessed() || !intro_sets.empty() ){
      return;
    }
  }
  Trace("sets") << "Done check normal forms" << std::endl;
}

void CardinalityExtension::checkNormalForm( Node eqc, std::vector< Node >& intro_sets ){
  TypeNode tn = eqc.getType();
  Trace("sets") << "Compute normal form for " << eqc << std::endl;
  Trace("sets-nf") << "Compute N " << eqc << "..." << std::endl;
  if( eqc==d_eqc_emptyset[tn] ){
    d_nf[eqc].clear();
    Trace("sets-nf") << "----> N " << eqc << " => {}" << std::endl;
    return;
  }
  //flat/normal forms are sets of equivalence classes
  Node base;
  std::vector< Node > comps;
  std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_ff.find( eqc );
  if( it!=d_ff.end() ){
    for( std::map< Node, std::vector< Node > >::iterator itf = it->second.begin(); itf != it->second.end(); ++itf ){
      std::sort( itf->second.begin(), itf->second.end() );
      if( base.isNull() ){
        base = itf->first;
      }else{
        comps.push_back( itf->first );
      }
      Trace("sets-nf") << "  F " << itf->first << " : ";
      if( Trace.isOn("sets-nf") ){
        Trace("sets-nf") << "{ ";
        for( unsigned k=0; k<itf->second.size(); k++ ){
          if( k>0 ){ Trace("sets-nf") << ", "; }
          Trace("sets-nf") << "[" << itf->second[k] << "]";
        }
        Trace("sets-nf") << " }" << std::endl;
      }
      Trace("sets-nf-debug") << " ...";
      debugPrintSet( itf->first, "sets-nf-debug" );
      Trace("sets-nf-debug") << std::endl;
    }
  }else{
    Trace("sets-nf") << "(no flat forms)" << std::endl;
  }

  Assert( d_nf.find( eqc )==d_nf.end() );
  bool success = true;
  Node emp_set = getEmptySet(tn);
  if( !base.isNull() ){
    for( unsigned j=0, csize = comps.size(); j<csize; j++ ){
      //compare if equal
      std::vector< Node > c;
      c.push_back( base );
      c.push_back( comps[j] );
      std::vector< Node > only[2];
      std::vector< Node > common;
      Trace("sets-nf-debug") << "Compare venn regions of " << base << " vs " << comps[j] << std::endl;
      unsigned k[2] = { 0, 0 };
      while( k[0]<d_ff[eqc][c[0]].size() || k[1]<d_ff[eqc][c[1]].size() ){
        bool proc = true;
        for( unsigned e=0; e<2; e++ ){
          if( k[e]==d_ff[eqc][c[e]].size() ){
            for( ; k[1-e]<d_ff[eqc][c[1-e]].size(); ++k[1-e] ){
              only[1-e].push_back( d_ff[eqc][c[1-e]][k[1-e]] );
            }
            proc = false;
          }
        }
        if( proc ){
          if( d_ff[eqc][c[0]][k[0]]==d_ff[eqc][c[1]][k[1]] ){
            common.push_back( d_ff[eqc][c[0]][k[0]] );
            k[0]++;
            k[1]++;
          }else if( d_ff[eqc][c[0]][k[0]]<d_ff[eqc][c[1]][k[1]] ){
            only[0].push_back( d_ff[eqc][c[0]][k[0]] );
            k[0]++;
          }else{
            only[1].push_back( d_ff[eqc][c[1]][k[1]] );
            k[1]++;
          }
        }
      }
      if( !only[0].empty() || !only[1].empty() ){
        if( Trace.isOn("sets-nf-debug") ){
          Trace("sets-nf-debug") << "Unique venn regions : " << std::endl;
          for( unsigned e=0; e<2; e++ ){
            Trace("sets-nf-debug") << "  " << c[e] << " : { ";
            for( unsigned l=0; l<only[e].size(); l++ ){
              if( l>0 ){ Trace("sets-nf-debug") << ", "; }
              Trace("sets-nf-debug") << "[" << only[e][l] << "]";
            }
            Trace("sets-nf-debug") << " }" << std::endl;
          }
        }
        //try to make one empty, prefer the unique ones first
        for( unsigned e=0; e<3; e++ ){
          unsigned sz = e==2 ? common.size() : only[e].size();
          for( unsigned l=0; l<sz; l++ ){
            Node r = e==2 ? common[l] : only[e][l];
            Trace("sets-nf-debug") << "Try split empty : " << r << std::endl;
            Trace("sets-nf-debug") << "         actual : ";
            debugPrintSet( r, "sets-nf-debug" );
            Trace("sets-nf-debug") << std::endl;
            Assert( !ee_areEqual( r, emp_set ) );
            if( !ee_areDisequal( r, emp_set ) && ( d_pol_mems[0].find( r )==d_pol_mems[0].end() || d_pol_mems[0][r].empty() ) ){
              //guess that its equal empty if it has no explicit members
              Trace("sets-nf") << " Split empty : " << r << std::endl;
              Trace("sets-nf") << "Actual Split : ";
              debugPrintSet( r, "sets-nf" );
              Trace("sets-nf") << std::endl;
              d_parent.split( r.eqNode( emp_set ), 1 );
              Assert( d_parent.hasProcessed() );
              return;
            }
          }
        }
        for( unsigned l=0; l<only[0].size(); l++ ){
          for( unsigned m=0; m<only[1].size(); m++ ){
            bool disjoint = false;
            Trace("sets-nf-debug") << "Try split " << only[0][l] << " against " << only[1][m] << std::endl;
            //split them
            for( unsigned e=0; e<2; e++ ){
              Node r1 = e==0 ? only[0][l] : only[1][m];
              Node r2 = e==0 ? only[1][m] : only[0][l];
              //check if their intersection exists modulo equality
              std::map< Node, Node >::iterator itb = d_bop_index[INTERSECTION][r1].find( r2 );
              if( itb!=d_bop_index[INTERSECTION][r1].end() ){
                Trace("sets-nf-debug") << "Split term already exists, but not in cardinality graph : " << itb->second << ", should be empty." << std::endl;
                //their intersection is empty (probably?)
                // e.g. these are two disjoint venn regions, proceed to next pair
                Assert( ee_areEqual( emp_set, itb->second ) );
                disjoint = true;
                break;
              }
            }
            if( !disjoint ){
              //simply introduce their intersection
              Assert( only[0][l]!=only[1][m] );
              Node kca = getProxy( only[0][l] );
              Node kcb = getProxy( only[1][m] );
              Node intro = Rewriter::rewrite( nm->mkNode( INTERSECTION, kca, kcb ) );
              Trace("sets-nf") << "   Intro split : " << only[0][l] << " against " << only[1][m] << ", term is " << intro << std::endl;
              intro_sets.push_back( intro );
              Assert( !d_equalityEngine.hasTerm( intro ) );
              return;
            }
          }
        }
        //should never get here
        success = false;
      }
    }
    if( success ){
      //normal form is flat form of base
      d_nf[eqc].insert( d_nf[eqc].end(), d_ff[eqc][base].begin(), d_ff[eqc][base].end() );
      Trace("sets-nf") << "----> N " << eqc << " => F " << base << std::endl;
    }else{
      Trace("sets-nf") << "failed to build N " << eqc << std::endl;
    }
  }else{
    // must ensure disequal from empty
    if (!eqc.isConst() && !ee_areDisequal(eqc, emp_set)
        && (d_pol_mems[0].find(eqc) == d_pol_mems[0].end()
            || d_pol_mems[0][eqc].empty()))
    {
      Trace("sets-nf-debug") << "Split on leaf " << eqc << std::endl;
      split(eqc.eqNode(emp_set));
      success = false;
    }
    else
    {
      // normal form is this equivalence class
      d_nf[eqc].push_back(eqc);
      Trace("sets-nf") << "----> N " << eqc << " => { " << eqc << " }"
                        << std::endl;
    }
  }
  if( !success ){
    Assert( d_parent.hasProcessed() );
    return;
  }
  //send to parents
  std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( eqc );
  if( itn==d_nvar_sets.end() ){
    // no parents
    return;
  }
  std::map< Node, std::map< Node, bool > > parents_proc;
  for( unsigned j=0; j<itn->second.size(); j++ ){
    Node n = itn->second[j];
    Trace("sets-nf-debug") << "Carry nf for term " << n << std::endl;
    if( d_card_parent[n].empty() ){
      // nothing to do
      continue;
    }
    Assert( d_card_base.find( n )!=d_card_base.end() );
    Node cbase = d_card_base[n];
    Trace("sets-nf-debug") << "Card base is " << cbase << std::endl;
    for( const Node& p : d_card_parent[n] ){
      Trace("sets-nf-debug") << "Check parent " << p << std::endl;
      if( parents_proc[cbase].find( p )!=parents_proc[cbase].end() ){
        Trace("sets-nf-debug") << "..already processed parent " << p << " for " << cbase << std::endl;
        continue;
      }
      parents_proc[cbase][p] = true;
      Trace("sets-nf-debug") << "Carry nf to parent ( " << cbase << ", [" << p << "] ), from " << n << "..." << std::endl;

      for( unsigned i=0; i<d_nf[eqc].size(); i++ ){
        if( std::find( d_ff[p][cbase].begin(), d_ff[p][cbase].end(), d_nf[eqc][i] )==d_ff[p][cbase].end() ){
          d_ff[p][cbase].insert( d_ff[p][cbase].end(), d_nf[eqc].begin(), d_nf[eqc].end() );
        }else{
          //if it is a duplicate venn region, it must be empty since it is coming from syntactically disjoint siblings TODO?
        }
      }
    }
  }
}

void CardinalityExtension::checkMinCard( std::vector< Node >& lemmas ) {
  NodeManager * nm = NodeManager::currentNM();
  for( int i=(int)(d_set_eqc.size()-1); i>=0; i-- ){
    Node eqc = d_set_eqc[i];
    TypeNode tn = eqc.getType().getSetElementType();
    if (d_t_card_enabled.find(tn) == d_t_card_enabled.end())
    {
      // cardinality is not enabled for this type, skip
      continue;
    }
    //get members in class
    std::map< Node, std::map< Node, Node > >::iterator itm = d_pol_mems[0].find( eqc );
    if( itm!=d_pol_mems[0].end() ){
      std::vector< Node > exp;
      std::vector< Node > members;
      Node cardTerm;
      std::map< Node, Node >::iterator it = d_eqc_to_card_term.find( eqc );
      if( it!=d_eqc_to_card_term.end() ){
        cardTerm = it->second;
      }else{
        cardTerm = nm->mkNode( CARD, eqc );
      }
      for( std::map< Node, Node >::iterator itmm = itm->second.begin(); itmm != itm->second.end(); ++itmm ){
        members.push_back( itmm->first );
        exp.push_back( nm->mkNode( MEMBER, itmm->first, cardTerm[0] ) );
      }
      if( members.size()>1 ){
        exp.push_back( nm->mkNode( DISTINCT, members ) );
      }
      if( !members.empty() ){
        Node conc = nm->mkNode( GEQ, cardTerm, nm->mkConst( Rational( members.size() ) ) );
        Node lem = nm->mkNode( IMPLIES, exp.size()==1 ? exp[0] : nm->mkNode( AND, exp ), conc );
        Trace("sets-lemma") << "Sets::Lemma : " << lem << " by mincard" << std::endl;
        lemmas.push_back( lem );
      }
    }
  }
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
