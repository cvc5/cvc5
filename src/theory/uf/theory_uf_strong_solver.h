/*********************                                                        */
/*! \file theory_uf_strong_solver.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory uf strong solver
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_STRONG_SOLVER_H
#define __CVC4__THEORY_UF_STRONG_SOLVER_H

#include "theory/theory.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"

#include "util/statistics_registry.h"

namespace CVC4 {

class SortInference;

namespace theory {

class SubsortSymmetryBreaker;

namespace uf {

class TheoryUF;
class DisequalityPropagator;

class StrongSolverTheoryUF{
protected:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashMap<TypeNode, bool, TypeNodeHashFunction> TypeNodeBoolMap;
public:
  /** information for incremental conflict/clique finding for a particular sort */
  class SortModel {
  private:
    std::map< Node, std::vector< int > > d_totality_lems;
    std::map< TypeNode, std::map< int, std::vector< Node > > > d_sym_break_terms;
    std::map< Node, int > d_sym_break_index;
  public:
    /** a partition of the current equality graph for which cliques can occur internally */
    class Region {
    public:
      /** conflict find pointer */
      SortModel* d_cf;
      /** information stored about each node in region */
      class RegionNodeInfo {
      public:
        /** disequality list for node */
        class DiseqList {
        public:
          DiseqList( context::Context* c ) : d_size( c, 0 ), d_disequalities( c ){}
          ~DiseqList(){}
          context::CDO< unsigned > d_size;
          NodeBoolMap d_disequalities;
          void setDisequal( Node n, bool valid ){
            Assert( d_disequalities.find( n )==d_disequalities.end() || d_disequalities[n]!=valid );
            d_disequalities[ n ] = valid;
            d_size = d_size + ( valid ? 1 : -1 );
          }
        };
      private:
        DiseqList d_internal;
        DiseqList d_external;
      public:
        /** constructor */
        RegionNodeInfo( context::Context* c ) :
          d_internal( c ), d_external( c ), d_valid( c, true ){
          d_disequalities[0] = &d_internal;
          d_disequalities[1] = &d_external;
        }
        ~RegionNodeInfo(){}
        context::CDO< bool > d_valid;
        DiseqList* d_disequalities[2];

        int getNumDisequalities() { return d_disequalities[0]->d_size + d_disequalities[1]->d_size; }
        int getNumExternalDisequalities() { return d_disequalities[0]->d_size; }
        int getNumInternalDisequalities() { return d_disequalities[1]->d_size; }
      };
      ///** end class RegionNodeInfo */
    private:
      context::CDO< unsigned > d_testCliqueSize;
      context::CDO< unsigned > d_splitsSize;
    public:
      //a postulated clique
      NodeBoolMap d_testClique;
      //disequalities needed for this clique to happen
      NodeBoolMap d_splits;
    private:
      //number of valid representatives in this region
      context::CDO< unsigned > d_reps_size;
      //total disequality size (external)
      context::CDO< unsigned > d_total_diseq_external;
      //total disequality size (internal)
      context::CDO< unsigned > d_total_diseq_internal;
    private:
      /** set rep */
      void setRep( Node n, bool valid );
    public:
      //constructor
      Region( SortModel* cf, context::Context* c ) : d_cf( cf ), d_testCliqueSize( c, 0 ),
        d_splitsSize( c, 0 ), d_testClique( c ), d_splits( c ), d_reps_size( c, 0 ),
        d_total_diseq_external( c, 0 ), d_total_diseq_internal( c, 0 ), d_valid( c, true ) {
      }
      virtual ~Region(){}
      //region node infomation
      std::map< Node, RegionNodeInfo* > d_nodes;
      //whether region is valid
      context::CDO< bool > d_valid;
    public:
      /** add rep */
      void addRep( Node n );
      //take node from region
      void takeNode( Region* r, Node n );
      //merge with other region
      void combine( Region* r );
      /** merge */
      void setEqual( Node a, Node b );
      //set n1 != n2 to value 'valid', type is whether it is internal/external
      void setDisequal( Node n1, Node n2, int type, bool valid );
    public:
      //get num reps
      int getNumReps() { return d_reps_size; }
      //get test clique size
      int getTestCliqueSize() { return d_testCliqueSize; }
      // has representative
      bool hasRep( Node n ) { return d_nodes.find( n )!=d_nodes.end() && d_nodes[n]->d_valid; }
      // is disequal
      bool isDisequal( Node n1, Node n2, int type );
      /** get must merge */
      bool getMustCombine( int cardinality );
      /** has splits */
      bool hasSplits() { return d_splitsSize>0; }
      /** get representatives */
      void getRepresentatives( std::vector< Node >& reps );
      /** get external disequalities */
      void getNumExternalDisequalities( std::map< Node, int >& num_ext_disequalities );
    public:
      /** check for cliques */
      bool check( Theory::Effort level, int cardinality, std::vector< Node >& clique );
      /** get candidate clique */
      bool getCandidateClique( int cardinality, std::vector< Node >& clique );
      //print debug
      void debugPrint( const char* c, bool incClique = false );
    };
  private:
    /** the type this model is for */
    TypeNode d_type;
    /** strong solver pointer */
    StrongSolverTheoryUF* d_thss;
    /** regions used to d_region_index */
    context::CDO< unsigned > d_regions_index;
    /** vector of regions */
    std::vector< Region* > d_regions;
    /** map from Nodes to index of d_regions they exist in, -1 means invalid */
    NodeIntMap d_regions_map;
    /** the score for each node for splitting */
    NodeIntMap d_split_score;
    /** regions used to d_region_index */
    context::CDO< unsigned > d_disequalities_index;
    /** list of all disequalities */
    std::vector< Node > d_disequalities;
    /** number of representatives in all regions */
    context::CDO< unsigned > d_reps;
  private:
    /** get number of disequalities from node n to region ri */
    int getNumDisequalitiesToRegion( Node n, int ri );
    /** get number of disequalities from Region r to other regions */
    void getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq );
    /** is valid */
    bool isValid( int ri ) { return ri>=0 && ri<(int)d_regions_index && d_regions[ ri ]->d_valid; }
    /** set split score */
    void setSplitScore( Node n, int s );
  private:
    /** check if we need to combine region ri */
    void checkRegion( int ri, bool checkCombine = true );
    /** force combine region */
    int forceCombineRegion( int ri, bool useDensity = true );
    /** merge regions */
    int combineRegions( int ai, int bi );
    /** move node n to region ri */
    void moveNode( Node n, int ri );
  private:
    /** allocate cardinality */
    void allocateCardinality( OutputChannel* out );
    /** add split 0 = no split, -1 = entailed disequality added, 1 = split added */
    int addSplit( Region* r, OutputChannel* out );
    /** add clique lemma */
    void addCliqueLemma( std::vector< Node >& clique, OutputChannel* out );
    /** add totality axiom */
    void addTotalityAxiom( Node n, int cardinality, OutputChannel* out );
  private:
    class NodeTrie {
      std::map< Node, NodeTrie > d_children;
    public:
      bool add( std::vector< Node >& n, unsigned i = 0 ){
        Assert( i<n.size() );
        if( i==(n.size()-1) ){
          bool ret = d_children.find( n[i] )==d_children.end();
          d_children[n[i]].d_children.clear();
          return ret;
        }else{
          return d_children[n[i]].add( n, i+1 );
        }
      }
    };
    std::map< int, NodeTrie > d_clique_trie;
    void addClique( int c, std::vector< Node >& clique );
  private:
    /** Are we in conflict */
    context::CDO<bool> d_conflict;
    /** cardinality */
    context::CDO< int > d_cardinality;
    /** maximum allocated cardinality */
    context::CDO< int > d_aloc_cardinality;
    /** cardinality lemma term */
    Node d_cardinality_term;
    /** cardinality totality terms */
    std::map< int, std::vector< Node > > d_totality_terms;
    /** cardinality literals */
    std::map< int, Node > d_cardinality_literal;
    /** cardinality lemmas */
    std::map< int, Node > d_cardinality_lemma;
    /** cardinality assertions (indexed by cardinality literals ) */
    NodeBoolMap d_cardinality_assertions;
    /** whether a positive cardinality constraint has been asserted */
    context::CDO< bool > d_hasCard;
    /** clique lemmas that have been asserted */
    std::map< int, std::vector< std::vector< Node > > > d_cliques;
    /** maximum negatively asserted cardinality */
    context::CDO< int > d_maxNegCard;
  private:
    /** apply totality */
    bool applyTotality( int cardinality );
    /** get totality lemma terms */
    Node getTotalityLemmaTerm( int cardinality, int i );
  public:
    SortModel( Node n, context::Context* c, context::UserContext* u, StrongSolverTheoryUF* thss );
    virtual ~SortModel(){}
    /** initialize */
    void initialize( OutputChannel* out );
    /** new node */
    void newEqClass( Node n );
    /** merge */
    void merge( Node a, Node b );
    /** assert terms are disequal */
    void assertDisequal( Node a, Node b, Node reason );
    /** are disequal */
    bool areDisequal( Node a, Node b );
    /** check */
    void check( Theory::Effort level, OutputChannel* out );
    /** propagate */
    void propagate( Theory::Effort level, OutputChannel* out );
    /** get next decision request */
    Node getNextDecisionRequest();
    /** minimize */
    bool minimize( OutputChannel* out, TheoryModel* m );
    /** assert cardinality */
    void assertCardinality( OutputChannel* out, int c, bool val );
    /** is in conflict */
    bool isConflict() { return d_conflict; }
    /** get cardinality */
    int getCardinality() { return d_cardinality; }
    /** get representatives */
    void getRepresentatives( std::vector< Node >& reps );
    /** has cardinality */
    bool hasCardinalityAsserted() { return d_hasCard; }
    /** get cardinality literal */
    Node getCardinalityLiteral( int c );
    /** get maximum negative cardinality */
    int getMaximumNegativeCardinality() { return d_maxNegCard.get(); }
    //print debug
    void debugPrint( const char* c );
    /** debug a model */
    void debugModel( TheoryModel* m );
  public:
    /** get number of regions (for debugging) */
    int getNumRegions();
  }; /** class SortModel */
private:
  /** The output channel for the strong solver. */
  OutputChannel* d_out;
  /** theory uf pointer */
  TheoryUF* d_th;
  /** Are we in conflict */
  context::CDO<bool> d_conflict;
  /** rep model structure, one for each type */
  std::map< TypeNode, SortModel* > d_rep_model;
  /** get sort model */
  SortModel* getSortModel( Node n );
private:
  /** allocated combined cardinality */
  context::CDO< int > d_aloc_com_card;
  /** combined cardinality constraints */
  std::map< int, Node > d_com_card_literal;
  /** combined cardinality assertions (indexed by cardinality literals ) */
  NodeBoolMap d_com_card_assertions;
  /** initialize */
  void initializeCombinedCardinality();
  /** allocateCombinedCardinality */
  void allocateCombinedCardinality();
  /** check */
  void checkCombinedCardinality();
private:
  /** disequality propagator */
  DisequalityPropagator* d_deq_prop;
  /** symmetry breaking techniques */
  SubsortSymmetryBreaker* d_sym_break;
public:
  StrongSolverTheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, TheoryUF* th);
  ~StrongSolverTheoryUF() {}
  /** get theory */
  TheoryUF* getTheory() { return d_th; }
  /** disequality propagator */
  DisequalityPropagator* getDisequalityPropagator() { return d_deq_prop; }
  /** symmetry breaker */
  SubsortSymmetryBreaker* getSymmetryBreaker() { return d_sym_break; }
  /** get sort inference module */
  SortInference* getSortInference();
  /** get default sat context */
  context::Context* getSatContext();
  /** get default output channel */
  OutputChannel& getOutputChannel();
  /** new node */
  void newEqClass( Node n );
  /** merge */
  void merge( Node a, Node b );
  /** assert terms are disequal */
  void assertDisequal( Node a, Node b, Node reason );
  /** assert node */
  void assertNode( Node n, bool isDecision );
  /** are disequal */
  bool areDisequal( Node a, Node b );
public:
  /** check */
  void check( Theory::Effort level );
  /** propagate */
  void propagate( Theory::Effort level );
  /** get next decision request */
  Node getNextDecisionRequest();
  /** preregister a term */
  void preRegisterTerm( TNode n );
  /** preregister a quantifier */
  void registerQuantifier( Node f );
  /** notify restart */
  void notifyRestart();
public:
  /** identify */
  std::string identify() const { return std::string("StrongSolverTheoryUF"); }
  //print debug
  void debugPrint( const char* c );
  /** debug a model */
  void debugModel( TheoryModel* m );
public:
  /** get is in conflict */
  bool isConflict() { return d_conflict; }
  /** get cardinality for node */
  int getCardinality( Node n );
  /** get cardinality for type */
  int getCardinality( TypeNode tn );
  /** get representatives */
  void getRepresentatives( Node n, std::vector< Node >& reps );
  /** minimize */
  bool minimize( TheoryModel* m = NULL );

  class Statistics {
  public:
    IntStat d_clique_conflicts;
    IntStat d_clique_lemmas;
    IntStat d_split_lemmas;
    IntStat d_disamb_term_lemmas;
    IntStat d_sym_break_lemmas;
    IntStat d_totality_lemmas;
    IntStat d_max_model_size;
    Statistics();
    ~Statistics();
  };
  /** statistics class */
  Statistics d_statistics;
};/* class StrongSolverTheoryUF */

class DisequalityPropagator
{
private:
  /** quantifiers engine */
  QuantifiersEngine* d_qe;
  /** strong solver */
  StrongSolverTheoryUF* d_ufss;
  /** true,false */
  Node d_true;
  Node d_false;
  /** check term t against equivalence class that t is disequal from */
  void checkEquivalenceClass( Node t, Node eqc );
public:
  DisequalityPropagator(QuantifiersEngine* qe, StrongSolverTheoryUF* ufss);
  /** merge */
  void merge( Node a, Node b );
  /** assert terms are disequal */
  void assertDisequal( Node a, Node b, Node reason );
  /** assert predicate */
  void assertPredicate( Node p, bool polarity );
public:
  class Statistics {
  public:
    IntStat d_propagations;
    Statistics();
    ~Statistics();
  };
  /** statistics class */
  Statistics d_statistics;
};

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_STRONG_SOLVER_H */
