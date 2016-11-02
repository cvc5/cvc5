/*********************                                                        */
/*! \file datatypes_sygus.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus utilities for theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/datatype.h"
#include "context/context.h"
#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
  class TermDbSygus;
} /* namespace quantifiers */

namespace datatypes {

class SygusSplit
{
private:
  quantifiers::TermDbSygus * d_tds;
  std::map< Node, std::vector< Node > > d_splits;
  std::map< TypeNode, std::vector< bool > > d_sygus_nred;
  std::map< TypeNode, std::map< int, std::map< int, std::vector< bool > > > > d_sygus_pc_nred;
  std::map< TypeNode, std::map< int, std::map< int, std::vector< int > > > > d_sygus_pc_arg_pos;
  std::map< TypeNode, TypeNode > d_register;  //stores sygus type
  // type to (rewritten) to original
  std::map< TypeNode, std::map< Node, Node > > d_gen_terms;
  std::map< TypeNode, std::map< Node, Node > > d_gen_terms_inactive;
  std::map< TypeNode, std::map< Node, bool > > d_gen_redundant;
private:
  /** register sygus type */
  void registerSygusType( TypeNode tn );
  /** register sygus operator */
  void registerSygusTypeConstructorArg( TypeNode tnn, const Datatype& dt, TypeNode tnnp, const Datatype& pdt, int csIndex, int sIndex );
  /** consider sygus split */
  bool considerSygusSplitKind( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Kind k, Kind parent, int arg );
  bool considerSygusSplitConst( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Node c, Kind parent, int arg );
  /** get first occurrence */
  int getFirstArgOccurrence( const DatatypeConstructor& c, const Datatype& dt );
  /** is arg datatype */
  bool isArgDatatype( const DatatypeConstructor& c, int i, const Datatype& dt );
  /** is type match */
  bool isTypeMatch( const DatatypeConstructor& c1, const DatatypeConstructor& c2 );
private:
  // generic cache
  bool isGenericRedundant( TypeNode tn, Node g, bool active = true );
public:
  SygusSplit( quantifiers::TermDbSygus * tds ) : d_tds( tds ){}
  ~SygusSplit(){}
  /** get sygus splits */
  void getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas );
};




class SygusSymBreak
{
private:
  quantifiers::TermDbSygus * d_tds;
  context::Context* d_context;
  class ProgSearch {
    typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
    typedef context::CDHashMap< Node, int, NodeHashFunction > IntMap;
    typedef context::CDHashMap< int, int > IntIntMap;
  private:
    SygusSymBreak * d_parent;
    Node getCandidateProgramAtDepth( int depth, Node prog, int curr_depth, Node parent, std::map< TypeNode, int >& var_count,
                                     std::vector< Node >& testers, std::map< Node, std::vector< Node > >& testers_u );
    bool processProgramDepth( int depth );
    bool processSubprograms( Node n, int depth, int odepth );
    bool assignTester( int tindex, Node n, int depth );
  public:
    ProgSearch( SygusSymBreak * p, Node a, context::Context* c ) :
      d_parent( p ), d_anchor( a ), d_testers( c ), d_watched_terms( c ), d_watched_count( c ), d_prog_depth( c, 0 ) {
      d_anchor_type = d_anchor.getType();
    }
    ~ProgSearch(){}
    Node d_anchor;
    NodeMap d_testers;
    IntMap d_watched_terms;
    IntIntMap d_watched_count;
    TypeNode d_anchor_type;
    context::CDO<int> d_prog_depth;
    void addTester( int tindex, Node n, Node exp );
  };
  std::map< Node, ProgSearch * > d_prog_search;
  std::map< TypeNode, std::map< Node, Node > > d_normalized_to_orig;
  std::map< TypeNode, std::map< Node, bool > > d_redundant;
  std::map< TypeNode, std::map< Node, int > > d_normalized_to_term_size;
  std::map< TypeNode, std::map< Node, std::vector< Node > > > d_lemmas_reported;
  //which testers to include in the lemma
  std::map< TypeNode, std::map< Node, std::vector< bool > > > d_lemma_inc_tst;
  //additional equalities to include in the lemma
  std::map< TypeNode, std::map< Node, std::vector< std::pair< int, int > > > > d_lemma_inc_eq;
  //other equalities
  std::map< TypeNode, Node > d_anchor_var;
  std::map< TypeNode, std::map< Node, std::vector< Node > > > d_lemma_inc_eq_gr[2];
private:
  Node getAnchor( Node n );
  bool processCurrentProgram( Node a, TypeNode at, int depth, Node prog,
                              std::vector< Node >& testers, std::map< Node, std::vector< Node > >& testers_u,
                              std::map< TypeNode, int >& var_count );
  bool processConstantArg( TypeNode tnp, const Datatype & pdt, int pc, Kind k, int i, Node arg, std::map< unsigned, bool >& rlv );
  void collectTesters( Node tst, std::map< Node, std::vector< Node > >& testers_u, std::vector< Node >& testers, std::map< Node, bool >& irrlv_tst );
  void collectSubterms( Node n, Node tst_curr, std::map< Node, std::vector< Node > >& testers_u, std::map< Node, std::vector< Node > >& nodes );
  bool isSeparation( Node rep_prog, Node tst_curr, std::map< Node, std::vector< Node > >& testers_u, std::vector< Node >& rlv_testers );
  Node getSeparationTemplate( TypeNode tn, Node rep_prog, Node anc_var, int& status );
public:
  SygusSymBreak( quantifiers::TermDbSygus * tds, context::Context* c );
  ~SygusSymBreak();
  /** add tester */
  void addTester( int tindex, Node n, Node exp );
  /** lemmas we have generated */
  std::vector< Node > d_lemmas;
};

}
}
}

#endif
