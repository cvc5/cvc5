/*********************                                                        */
/*! \file theory_uf_instantiator.h
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
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_INSTANTIATOR_H
#define __CVC4__THEORY_UF_INSTANTIATOR_H

#include "theory/uf/inst_strategy.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

#include "util/stats.h"
#include "theory/uf/theory_uf.h"

namespace CVC4 {
namespace theory {

class TermDb;

namespace uf {

class InstantiatorTheoryUf;

//equivalence class info
class EqClassInfo
{
public:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDChunkList<Node> NodeList;
public:
  //a list of operators that occur as top symbols in this equivalence class
  //  Efficient E-Matching for SMT Solvers: "funs"
  BoolMap d_funs;
  //a list of operators f for which a term of the form f( ... t ... ) exists
  //  Efficient E-Matching for SMT Solvers: "pfuns"
  BoolMap d_pfuns;
  //a list of equivalence classes that are disequal
  BoolMap d_disequal;
public:
  EqClassInfo( context::Context* c );
  ~EqClassInfo(){}
  //set member
  void setMember( Node n, TermDb* db );
  //has function "funs"
  bool hasFunction( Node op );
  //has parent "pfuns"
  bool hasParent( Node op );
  //merge with another eq class info
  void merge( EqClassInfo* eci );
};

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::InstMatchGenerator;
  friend class ::CVC4::theory::TermDb;
protected:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeLists;
  /** map to representatives used */
  std::map< Node, Node > d_ground_reps;
protected:
  /** instantiation strategies */
  InstStrategyUserPatterns* d_isup;
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* qe, Theory* th);
  ~InstantiatorTheoryUf() {}
  /** assertNode method */
  void assertNode( Node assertion );
  /** Pre-register a term.  Done one time for a Node, ever. */
  void preRegisterTerm( Node t );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
private:
  /** reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** calculate matches for quantifier f at effort */
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  /** statistics class */
  class Statistics {
  public:
    //IntStat d_instantiations;
    IntStat d_instantiations_ce_solved;
    IntStat d_instantiations_e_induced;
    IntStat d_instantiations_user_pattern;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_auto_gen_min;
    IntStat d_splits;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
public:
  /** the base match */
  std::map< Node, InstMatch > d_baseMatch;
private:
  //for each equivalence class
  std::map< Node, EqClassInfo* > d_eqc_ops;
public:
  /** general queries about equality */
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  Node getInternalRepresentative( Node a );
  /** new node */
  void newEqClass( TNode n );
  /** merge */
  void merge( TNode a, TNode b );
  /** assert terms are disequal */
  void assertDisequal( TNode a, TNode b, TNode reason );
  /** get equivalence class info */
  EqClassInfo* getEquivalenceClassInfo( Node n );
  EqClassInfo* getOrCreateEquivalenceClassInfo( Node n );
private:
  typedef std::vector< std::pair< Node, int > > InvertedPathString;
  typedef std::pair< InvertedPathString, InvertedPathString > IpsPair;
  /** Parent/Child Pairs (for efficient E-matching)
      So, for example, if we have the pattern f( g( x ) ), then d_pc_pairs[g][f][f( g( x ) )] = { f.0 }.
  */
  std::map< Node, std::map< Node, std::map< Node, std::vector< InvertedPathString > > > > d_pc_pairs;
  /** Parent/Parent Pairs (for efficient E-matching) */
  std::map< Node, std::map< Node, std::map< Node, std::vector< IpsPair > > > > d_pp_pairs;
  /** list of all candidate generators for each operator */
  std::map< Node, std::vector< CandidateGenerator* > > d_cand_gens;
  /** map from patterns to candidate generators */
  std::map< Node, std::vector< CandidateGenerator* > > d_pat_cand_gens;
  /** helper functions */
  void registerPatternElementPairs2( Node opat, Node pat, InvertedPathString& ips,
                                     std::map< Node, std::vector< std::pair< Node, InvertedPathString > > >& ips_map );
  void registerPatternElementPairs( Node pat );
  /** compute candidates for pc pairs */
  void computeCandidatesPcPairs( Node a, Node b );
  /** compute candidates for pp pairs */
  void computeCandidatesPpPairs( Node a, Node b );
  /** collect terms based on inverted path string */
  void collectTermsIps( InvertedPathString& ips, std::vector< Node >& terms, int index = 0 );
  bool collectParentsTermsIps( Node n, Node f, int arg, std::vector< Node >& terms, bool addRep, bool modEq = true );
public:
  /** Register candidate generator cg for pattern pat. (for use with efficient e-matching)
      This request will ensure that calls will be made to cg->addCandidate( n ) for all
      ground terms n that are relevant for matching with pat.
  */
  void registerCandidateGenerator( CandidateGenerator* cg, Node pat );
private:
  /** triggers */
  std::map< Node, std::vector< Trigger* > > d_op_triggers;
public:
  /** register trigger (for eager quantifier instantiation) */
  void registerTrigger( Trigger* tr, Node op );
public:
  /** output eq class */
  void outputEqClass( const char* c, Node n );
  /** output inverted path string */
  void outputInvertedPathString( const char* c, InvertedPathString& ips );
};/* class InstantiatorTheoryUf */

/** equality query object using instantiator theory uf */
class EqualityQueryInstantiatorTheoryUf : public EqualityQuery
{
private:
  /** pointer to instantiator uf class */
  InstantiatorTheoryUf* d_ith;
public:
  EqualityQueryInstantiatorTheoryUf( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~EqualityQueryInstantiatorTheoryUf(){}
  /** general queries about equality */
  bool hasTerm( Node a ) { return d_ith->hasTerm( a ); }
  Node getRepresentative( Node a ) { return d_ith->getRepresentative( a ); }
  bool areEqual( Node a, Node b ) { return d_ith->areEqual( a, b ); }
  bool areDisequal( Node a, Node b ) { return d_ith->areDisequal( a, b ); }
  Node getInternalRepresentative( Node a ) { return d_ith->getInternalRepresentative( a ); }
}; /* EqualityQueryInstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */
