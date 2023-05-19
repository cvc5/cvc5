/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of UF with cardinality.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY_UF_STRONG_SOLVER_H
#define CVC5__THEORY_UF_STRONG_SOLVER_H

#include "context/cdhashmap.h"
#include "context/context.h"
#include "smt/env_obj.h"
#include "theory/decision_strategy.h"
#include "theory/theory.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

class TheoryUF;

/**
 * This module implements a theory solver for UF with cardinality constraints.
 * For high level details, see Reynolds et al "Finite Model Finding in SMT",
 * CAV 2013, or Reynolds dissertation "Finite Model Finding in Satisfiability
 * Modulo Theories".
 */
class CardinalityExtension : protected EnvObj
{
 protected:
  typedef context::CDHashMap<Node, bool> NodeBoolMap;
  typedef context::CDHashMap<Node, int> NodeIntMap;

 public:
  /**
   * Information for incremental conflict/clique finding for a
   * particular sort.
   */
  class SortModel : protected EnvObj
  {
   private:
    std::map< Node, std::vector< int > > d_totality_lems;
    std::map< TypeNode, std::map< int, std::vector< Node > > > d_sym_break_terms;
    std::map< Node, int > d_sym_break_index;

   public:
    /**
     * A partition of the current equality graph for which cliques
     * can occur internally.
     */
    class Region
    {
     public:
      /** information stored about each node in region */
      class RegionNodeInfo {
      public:
        /** disequality list for node */
        class DiseqList {
        public:
         DiseqList(context::Context* c) : d_size(c, 0), d_disequalities(c) {}
         ~DiseqList() {}

         void setDisequal(Node n, bool valid)
         {
           Assert((!isSet(n)) || getDisequalityValue(n) != valid);
           d_disequalities[n] = valid;
           d_size = d_size + (valid ? 1 : -1);
          }
          bool isSet(Node n) const {
            return d_disequalities.find(n) != d_disequalities.end();
          }
          bool getDisequalityValue(Node n) const {
            Assert(isSet(n));
            return (*(d_disequalities.find(n))).second;
          }

          int size() const { return d_size; }
          
          typedef NodeBoolMap::iterator iterator;
          iterator begin() { return d_disequalities.begin(); }
          iterator end() { return d_disequalities.end(); }

        private:
         context::CDO<int> d_size;
         NodeBoolMap d_disequalities;
        }; /* class DiseqList */
       public:
        /** constructor */
        RegionNodeInfo(context::Context* c)
            : d_internal(c), d_external(c), d_valid(c, true)
        {
          d_disequalities[0] = &d_internal;
          d_disequalities[1] = &d_external;
        }
        ~RegionNodeInfo(){}
       
        int getNumDisequalities() const {
          return d_disequalities[0]->size() + d_disequalities[1]->size();
        }
        int getNumExternalDisequalities() const {
          return d_disequalities[0]->size();
        }
        int getNumInternalDisequalities() const {
          return d_disequalities[1]->size();
        }

        bool valid() const { return d_valid; }
        void setValid(bool valid) { d_valid = valid; }

        DiseqList* get(unsigned i) { return d_disequalities[i]; }

       private:
        DiseqList d_internal;
        DiseqList d_external;
        context::CDO<bool> d_valid;
        DiseqList* d_disequalities[2];
      }; /* class RegionNodeInfo */

    private:
      /** conflict find pointer */
      SortModel* d_cf;

      context::CDO<size_t> d_testCliqueSize;
      context::CDO<unsigned> d_splitsSize;
      //a postulated clique
      NodeBoolMap d_testClique;
      //disequalities needed for this clique to happen
      NodeBoolMap d_splits;
      //number of valid representatives in this region
      context::CDO<size_t> d_reps_size;
      //total disequality size (external)
      context::CDO<unsigned> d_total_diseq_external;
      //total disequality size (internal)
      context::CDO<unsigned> d_total_diseq_internal;
      /** set rep */
      void setRep( Node n, bool valid );
      //region node infomation
      std::map< Node, RegionNodeInfo* > d_nodes;
      //whether region is valid
      context::CDO<bool> d_valid;

     public:
      //constructor
      Region(SortModel* cf, context::Context* c);
      virtual ~Region();

      typedef std::map< Node, RegionNodeInfo* >::iterator iterator;
      iterator begin() { return d_nodes.begin(); }
      iterator end() { return d_nodes.end(); }

      typedef NodeBoolMap::iterator split_iterator;
      split_iterator begin_splits() { return d_splits.begin(); }
      split_iterator end_splits() { return d_splits.end(); }

      /** Returns a RegionInfo. */
      RegionNodeInfo* getRegionInfo(Node n) {
        Assert(d_nodes.find(n) != d_nodes.end());
        return (* (d_nodes.find(n))).second;
      }

      /** Returns whether or not d_valid is set in current context. */
      bool valid() const { return d_valid; }

      /** Sets d_valid to the value valid in the current context.*/
      void setValid(bool valid) { d_valid = valid; }

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
      //get num reps
      size_t getNumReps() const { return d_reps_size; }
      //get test clique size
      size_t getTestCliqueSize() const { return d_testCliqueSize; }
      // has representative
      bool hasRep( Node n ) {
        return d_nodes.find(n) != d_nodes.end() && d_nodes[n]->valid();
      }
      // is disequal
      bool isDisequal( Node n1, Node n2, int type );
      /** get must merge */
      bool getMustCombine( int cardinality );
      /** has splits */
      bool hasSplits() { return d_splitsSize>0; }
      /** get external disequalities */
      void getNumExternalDisequalities(std::map< Node, int >& num_ext_disequalities );
      /** check for cliques */
      bool check( Theory::Effort level, int cardinality, std::vector< Node >& clique );
      //print debug
      void debugPrint( const char* c, bool incClique = false );

      // Returns the first key in d_nodes.
      Node frontKey() const { return d_nodes.begin()->first; }
    }; /* class Region */

   private:
    /** the type this model is for */
    TypeNode d_type;
    /** Reference to the state object */
    TheoryState& d_state;
    /** Reference to the inference manager */
    TheoryInferenceManager& d_im;
    /** Pointer to the cardinality extension that owns this. */
    CardinalityExtension* d_thss;
    /** regions used to d_region_index */
    context::CDO<size_t> d_regions_index;
    /** vector of regions */
    std::vector< Region* > d_regions;
    /** map from Nodes to index of d_regions they exist in, -1 means invalid */
    NodeIntMap d_regions_map;
    /** the score for each node for splitting */
    NodeIntMap d_split_score;
    /** number of valid disequalities in d_disequalities */
    context::CDO<unsigned> d_disequalities_index;
    /** list of all disequalities */
    std::vector< Node > d_disequalities;
    /** number of representatives in all regions */
    context::CDO<unsigned> d_reps;

    /** get number of disequalities from node n to region ri */
    int getNumDisequalitiesToRegion( Node n, int ri );
    /** get number of disequalities from Region r to other regions */
    void getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq );
    /** is valid */
    bool isValid( int ri ) {
      return ri>=0 && ri<(int)d_regions_index && d_regions[ ri ]->valid();
    }
    /** set split score */
    void setSplitScore( Node n, int s );
    /** check if we need to combine region ri */
    void checkRegion( int ri, bool checkCombine = true );
    /** force combine region */
    int forceCombineRegion( int ri, bool useDensity = true );
    /** merge regions */
    int combineRegions( int ai, int bi );
    /** move node n to region ri */
    void moveNode( Node n, int ri );
    /** allocate cardinality */
    void allocateCardinality();
    /**
     * Add splits. Returns
     *   0 = no split,
     *  -1 = entailed disequality added, or
     *   1 = split added.
     */
    int addSplit(Region* r);
    /** add clique lemma */
    void addCliqueLemma(std::vector<Node>& clique);
    /** cardinality */
    context::CDO<uint32_t> d_cardinality;
    /** cardinality literals */
    std::map<uint32_t, Node> d_cardinality_literal;
    /** whether a positive cardinality constraint has been asserted */
    context::CDO<bool> d_hasCard;
    /** clique lemmas that have been asserted */
    std::map< int, std::vector< std::vector< Node > > > d_cliques;
    /** maximum negatively asserted cardinality */
    context::CDO<uint32_t> d_maxNegCard;
    /** list of fresh representatives allocated */
    std::vector< Node > d_fresh_aloc_reps;
    /** whether we are initialized */
    context::CDO<bool> d_initialized;
    /** simple check cardinality */
    void simpleCheckCardinality();

   public:
    SortModel(Env& env,
              TypeNode tn,
              TheoryState& state,
              TheoryInferenceManager& im,
              CardinalityExtension* thss);
    virtual ~SortModel();
    /** initialize */
    void initialize();
    /** new node */
    void newEqClass( Node n );
    /** merge */
    void merge( Node a, Node b );
    /** assert terms are disequal */
    void assertDisequal( Node a, Node b, Node reason );
    /** are disequal */
    bool areDisequal( Node a, Node b );
    /** check */
    void check(Theory::Effort level);
    /** presolve */
    void presolve();
    /** assert cardinality */
    void assertCardinality(uint32_t c, bool val);
    /** get cardinality */
    uint32_t getCardinality() const { return d_cardinality; }
    /** has cardinality */
    bool hasCardinalityAsserted() const { return d_hasCard; }
    /** get cardinality term */
    TypeNode getType() const { return d_type; }
    /** get cardinality literal */
    Node getCardinalityLiteral(uint32_t c);
    /** get maximum negative cardinality */
    uint32_t getMaximumNegativeCardinality() const
    {
      return d_maxNegCard.get();
    }
    //print debug
    void debugPrint( const char* c );
    /**
     * Check at last call effort. This will verify that the model is minimal.
     * This return lemmas if there are terms in the model that the cardinality
     * extension was not notified of.
     *
     * @return false if current model is not minimal. In this case, lemmas are
     * sent on the output channel of the UF theory.
     */
    bool checkLastCall();
    /** get number of regions (for debugging) */
    int getNumRegions();

   private:
    /**
     * Decision strategy for cardinality constraints. This asserts
     * the minimal constraint positively in the SAT context. For details, see
     * Section 6.3 of Reynolds et al, "Constraint Solving for Finite Model
     * Finding in SMT Solvers", TPLP 2017.
     */
    class CardinalityDecisionStrategy : public DecisionStrategyFmf
    {
     public:
      CardinalityDecisionStrategy(Env& env, TypeNode type, Valuation valuation);
      /** make literal (the i^th combined cardinality literal) */
      Node mkLiteral(unsigned i) override;
      /** identify */
      std::string identify() const override;
     private:
      /** The type we are considering cardinality constraints for */
      TypeNode d_type;
    };
    /** cardinality decision strategy */
    std::unique_ptr<CardinalityDecisionStrategy> d_c_dec_strat;
  }; /** class SortModel */

 public:
  CardinalityExtension(Env& env,
                       TheoryState& state,
                       TheoryInferenceManager& im,
                       TheoryUF* th);
  ~CardinalityExtension();
  /** get theory */
  TheoryUF* getTheory() { return d_th; }
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
  /** check */
  void check( Theory::Effort level );
  /** presolve */
  void presolve();
  /** preregister a term */
  void preRegisterTerm( TNode n );
  /** identify */
  std::string identify() const { return std::string("CardinalityExtension"); }
  //print debug
  void debugPrint( const char* c );
  /** get cardinality for node */
  int getCardinality( Node n );
  /** get cardinality for type */
  int getCardinality( TypeNode tn );
  /** has eqc */
  bool hasEqc(Node a);

  class Statistics {
   public:
    IntStat d_clique_conflicts;
    IntStat d_clique_lemmas;
    IntStat d_split_lemmas;
    IntStat d_max_model_size;
    Statistics(StatisticsRegistry& sr);
  };
  /** statistics class */
  Statistics d_statistics;

 private:
  /** get sort model */
  SortModel* getSortModel(Node n);
  /** initialize */
  void initializeCombinedCardinality();
  /** check */
  void checkCombinedCardinality();
  /** ensure eqc */
  void ensureEqc(SortModel* c, Node a);
  /** ensure eqc for all subterms of n */
  void ensureEqcRec(Node n);

  /** Reference to the state object */
  TheoryState& d_state;
  /** Reference to the inference manager */
  TheoryInferenceManager& d_im;
  /** theory uf pointer */
  TheoryUF* d_th;
  /** rep model structure, one for each type */
  std::map<TypeNode, SortModel*> d_rep_model;

  /** minimum positive combined cardinality */
  context::CDO<uint32_t> d_min_pos_com_card;
  /** Whether the field above has been set */
  context::CDO<bool> d_min_pos_com_card_set;
  /**
   * Decision strategy for combined cardinality constraints. This asserts
   * the minimal combined cardinality constraint positively in the SAT
   * context. It is enabled by the ufssFairness option. For details, see
   * the extension to multiple sorts in Section 6.3 of Reynolds et al,
   * "Constraint Solving for Finite Model Finding in SMT Solvers", TPLP 2017.
   */
  class CombinedCardinalityDecisionStrategy : public DecisionStrategyFmf
  {
   public:
    CombinedCardinalityDecisionStrategy(Env& env, Valuation valuation);
    /** make literal (the i^th combined cardinality literal) */
    Node mkLiteral(unsigned i) override;
    /** identify */
    std::string identify() const override;
  };
  /** combined cardinality decision strategy */
  std::unique_ptr<CombinedCardinalityDecisionStrategy> d_cc_dec_strat;
  /** Have we initialized combined cardinality? */
  context::CDO<bool> d_initializedCombinedCardinality;

  /** cardinality literals for which we have added */
  NodeBoolMap d_card_assertions_eqv_lemma;
  /** the master monotone type (if ufssFairnessMonotone enabled) */
  TypeNode d_tn_mono_master;
  std::map<TypeNode, bool> d_tn_mono_slave;
  /** The minimum positive asserted master cardinality */
  context::CDO<uint32_t> d_min_pos_tn_master_card;
  /** Whether the field above has been set */
  context::CDO<bool> d_min_pos_tn_master_card_set;
  /** relevant eqc */
  NodeBoolMap d_rel_eqc;
}; /* class CardinalityExtension */

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY_UF_STRONG_SOLVER_H */
