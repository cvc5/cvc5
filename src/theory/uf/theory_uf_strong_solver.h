/*********************                                                        */
/*! \file theory_uf_strong_solver.h
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
 ** \brief Theory uf strong solver
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_STRONG_SOLVER_H
#define __CVC4__THEORY_UF_STRONG_SOLVER_H

#include "theory/theory.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

#include "util/stats.h"

namespace CVC4 {
namespace theory {

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;

namespace uf {

class TheoryUF;

class StrongSolverTheoryUf{
protected:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDList<bool> BoolList;
  typedef context::CDHashMap<TypeNode, bool, TypeNodeHashFunction> TypeNodeBoolMap;
public:
  /** information for incremental conflict/clique finding for a particular sort */
  class ConflictFind {
  public:
    /** a partition of the current equality graph for which cliques can occur internally */
    class Region {
    public:
      /** conflict find pointer */
      ConflictFind* d_cf;
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
        RegionNodeInfo( context::Context* c ) : d_internal( c ), d_external( c ), d_valid( c, true ){
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
      //a postulated clique
      NodeBoolMap d_testClique;
      context::CDO< unsigned > d_testCliqueSize;
      //disequalities needed for this clique to happen
      NodeBoolMap d_splits;
      context::CDO< unsigned > d_splitsSize;
      /** get split */
      Node getBestSplit();
    private:
      //number of valid representatives in this region
      context::CDO< unsigned > d_reps_size;
      //total disequality size (external)
      context::CDO< unsigned > d_total_diseq_external;
      //total disequality size (internal)
      context::CDO< unsigned > d_total_diseq_internal;
    public:
      //constructor
      Region( ConflictFind* cf, context::Context* c ) : d_cf( cf ), d_testClique( c ), d_testCliqueSize( c, 0 ),
        d_splits( c ), d_splitsSize( c, 0 ), d_reps_size( c, 0 ), d_total_diseq_external( c, 0 ),
        d_total_diseq_internal( c, 0 ), d_valid( c, true ) {
      }
      ~Region(){}
      //region node infomation
      std::map< Node, RegionNodeInfo* > d_nodes;
      //whether region is valid
      context::CDO< bool > d_valid;
    public:
      //get num reps
      int getNumReps() { return d_reps_size; }
      // has representative
      bool hasRep( Node n ) { return d_nodes.find( n )!=d_nodes.end() && d_nodes[n]->d_valid; }
      //take node from region
      void takeNode( Region* r, Node n );
      //merge with other region
      void combine( Region* r );
      /** set rep */
      void setRep( Node n, bool valid );
      /** merge */
      void setEqual( Node a, Node b );
      //set n1 != n2 to value 'valid', type is whether it is internal/external
      void setDisequal( Node n1, Node n2, int type, bool valid );
      // is disequal
      bool isDisequal( Node n1, Node n2, int type );
    public:
      /** get must merge */
      bool getMustCombine( int cardinality );
      /** check for cliques */
      bool check( Theory::Effort level, int cardinality, std::vector< Node >& clique );
      /** has splits */
      bool hasSplits() { return d_splitsSize>0; }
      /** add split */
      void addSplit( OutputChannel* out );
      /** get representatives */
      void getRepresentatives( std::vector< Node >& reps );
      /** minimize */
      bool minimize( OutputChannel* out );
      /** get external disequalities */
      void getNumExternalDisequalities( std::map< Node, int >& num_ext_disequalities );
      //print debug
      void debugPrint( const char* c, bool incClique = false );
    };
  private:
    /** theory uf pointer */
    TheoryUF* d_th;
    /** regions used to d_region_index */
    context::CDO< unsigned > d_regions_index;
    /** vector of regions */
    std::vector< Region* > d_regions;
    /** map from Nodes to index of d_regions they exist in, -1 means invalid */
    NodeIntMap d_regions_map;
    /** regions used to d_region_index */
    context::CDO< unsigned > d_disequalities_index;
    /** list of all disequalities */
    std::vector< Node > d_disequalities;
    /** number of representatives in all regions */
    context::CDO< unsigned > d_reps;
    /** whether two terms are ambiguous (indexed by equalities) */
    NodeBoolMap d_term_amb;
  private:
    /** merge regions */
    void combineRegions( int ai, int bi );
    /** move node n to region ri */
    void moveNode( Node n, int ri );
    /** get number of disequalities from node n to region ri */
    int getNumDisequalitiesToRegion( Node n, int ri );
    /** get number of disequalities from Region r to other regions */
    void getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq );
    /** check if we need to combine region ri */
    bool checkRegion( int ri, bool rec = true );
    /** explain clique */
    void explainClique( std::vector< Node >& clique, OutputChannel* out );
    /** is valid */
    bool isValid( int ri ) { return ri>=0 && ri<(int)d_regions_index && d_regions[ ri ]->d_valid; }
    /** check ambiguous terms */
    bool disambiguateTerms( OutputChannel* out );
  private:
    /** cardinality operating with */
    context::CDO< int > d_cardinality;
    /** type */
    TypeNode d_type;
    /** cardinality lemma term */
    Node d_cardinality_lemma_term;
    /** cardinality literals */
    std::map< int, Node > d_cardinality_literal;
    /** cardinality lemmas */
    std::map< int, Node > d_cardinality_lemma;
    /** cardinality assertions (indexed by cardinality literals ) */
    NodeBoolMap d_cardinality_assertions;
  public:
    ConflictFind( TypeNode tn, context::Context* c, TheoryUF* th ) :
        d_th( th ), d_regions_index( c, 0 ), d_regions_map( c ), d_disequalities_index( c, 0 ),
        d_reps( c, 0 ), d_term_amb( c ), d_cardinality( c, 1 ), d_type( tn ),
        d_cardinality_assertions( c ), d_is_cardinality_set( c, false ),
        d_is_cardinality_requested_c( c, false ), d_is_cardinality_requested( false ), d_hasCard( c, false ){}
    ~ConflictFind(){}
    /** new node */
    void newEqClass( Node n );
    /** merge */
    void merge( Node a, Node b );
    /** assert terms are disequal */
    void assertDisequal( Node a, Node b, Node reason );
    /** assert cardinality */
    void assertCardinality( int c, bool val );
    /** whether cardinality has been asserted */
    bool hasCardinalityAsserted() { return d_hasCard; }
    /** check */
    void check( Theory::Effort level, OutputChannel* out );
    /** propagate */
    void propagate( Theory::Effort level, OutputChannel* out );
    //print debug
    void debugPrint( const char* c );
    /** set cardinality */
    void setCardinality( int c, OutputChannel* out );
    /** get cardinality */
    int getCardinality() { return d_cardinality; }
    /** get representatives */
    void getRepresentatives( std::vector< Node >& reps );
    /** get model basis term */
    Node getCardinalityTerm() { return d_cardinality_lemma_term; }
    /** minimize */
    bool minimize( OutputChannel* out );
    /** get cardinality lemma */
    Node getCardinalityLemma();
  public:
    /** get number of regions (for debugging) */
    int getNumRegions();
    /** is cardinality set */
    context::CDO< bool > d_is_cardinality_set;
    context::CDO< bool > d_is_cardinality_requested_c;
    bool d_is_cardinality_requested;
    /** whether a positive cardinality constraint has been asserted */
    context::CDO< bool > d_hasCard;
  }; /** class ConflictFind */
private:
  /** The output channel for the strong solver. */
  OutputChannel* d_out;
  /** theory uf pointer */
  TheoryUF* d_th;
  /** conflict find structure, one for each type */
  std::map< TypeNode, ConflictFind* > d_conf_find;
  /** all types */
  std::vector< TypeNode > d_conf_types;
  /** whether conflict find data structures have been initialized */
  TypeNodeBoolMap d_conf_find_init;
  /** pre register type */
  void preRegisterType( TypeNode tn );
  /** get conflict find */
  ConflictFind* getConflictFind( TypeNode tn );
public:
  StrongSolverTheoryUf(context::Context* c, context::UserContext* u, OutputChannel& out, TheoryUF* th);
  ~StrongSolverTheoryUf() {}
  /** new node */
  void newEqClass( Node n );
  /** merge */
  void merge( Node a, Node b );
  /** assert terms are disequal */
  void assertDisequal( Node a, Node b, Node reason );
  /** assert node */
  void assertNode( Node n, bool isDecision );
public:
  /** check */
  void check( Theory::Effort level );
  /** propagate */
  void propagate( Theory::Effort level );
  /** preregister a term */
  void preRegisterTerm( TNode n );
  /** preregister a quantifier */
  void registerQuantifier( Node f );
  /** notify restart */
  void notifyRestart();
public:
  /** identify */
  std::string identify() const { return std::string("StrongSolverTheoryUf"); }
  //print debug
  void debugPrint( const char* c );
public:
  /** get number of types */
  int getNumCardinalityTypes() { return (int)d_conf_types.size(); }
  /** get type */
  TypeNode getCardinalityType( int i ) { return d_conf_types[i]; }
  /** get cardinality for sort */
  int getCardinality( TypeNode t );
  /** get representatives */
  void getRepresentatives( TypeNode t, std::vector< Node >& reps );
  /** get cardinality term */
  Node getCardinalityTerm( TypeNode t );
  /** minimize */
  bool minimize();

  class Statistics {
  public:
    IntStat d_clique_lemmas;
    IntStat d_split_lemmas;
    IntStat d_disamb_term_lemmas;
    IntStat d_max_model_size;
    Statistics();
    ~Statistics();
  };
  /** statistics class */
  Statistics d_statistics;

  /** is relevant type */
  static bool isRelevantType( TypeNode t );
  /** involves relevant type */
  static bool involvesRelevantType( Node n );
};/* class StrongSolverTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_STRONG_SOLVER_H */
