/*********************                                                        */
/*! \file conjecture_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief conjecture generator class
 **/

#include "cvc4_private.h"

#ifndef CONJECTURE_GENERATOR_H
#define CONJECTURE_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/node_trie.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

//algorithm for computing candidate subgoals

class ConjectureGenerator;

// operator independent index of arguments for an EQC
class OpArgIndex
{
public:
  std::map< TNode, OpArgIndex > d_child;
  std::vector< TNode > d_ops;
  std::vector< TNode > d_op_terms;
  void addTerm( std::vector< TNode >& terms, TNode n, unsigned index = 0 );
  Node getGroundTerm( ConjectureGenerator * s, std::vector< TNode >& args );
  void getGroundTerms( ConjectureGenerator * s, std::vector< TNode >& terms );
};

class PatternTypIndex
{
public:
  std::vector< TNode > d_terms;
  std::map< TypeNode, std::map< unsigned, PatternTypIndex > > d_children;
  void clear() {
    d_terms.clear();
    d_children.clear();
  }
};

class SubstitutionIndex
{
public:
  //current variable, or ground EQC if d_children.empty()
  TNode d_var;
  std::map< TNode, SubstitutionIndex > d_children;
  //add substitution
  void addSubstitution( TNode eqc, std::vector< TNode >& vars, std::vector< TNode >& terms, unsigned i = 0 );
  //notify substitutions
  bool notifySubstitutions( ConjectureGenerator * s, std::map< TNode, TNode >& subs, TNode rhs, unsigned numVars, unsigned i = 0 );
};

class TermGenEnv;

class TermGenerator
{
 private:
  unsigned calculateGeneralizationDepth( TermGenEnv * s, std::map< TypeNode, std::vector< int > >& fvs );

 public:
  TermGenerator()
      : d_id(0),
        d_status(0),
        d_status_num(0),
        d_status_child_num(0),
        d_match_status(0),
        d_match_status_child_num(0),
        d_match_mode(0)
  {
  }
  TypeNode d_typ;
  unsigned d_id;
  //1 : consider as unique variable
  //2 : consider equal to another variable
  //5 : consider a function application
  unsigned d_status;
  int d_status_num;
  //for function applications: the number of children you have built
  int d_status_child_num;
  //children (pointers to TermGenerators)
  std::vector< unsigned > d_children;

  //match status
  int d_match_status;
  int d_match_status_child_num;
  //match mode bits
  //0 : different variables must have different matches
  //1 : variables must map to ground terms
  //2 : variables must map to non-ground terms
  unsigned d_match_mode;
  //children
  std::vector<std::map<TNode, TNodeTrie>::iterator> d_match_children;
  std::vector<std::map<TNode, TNodeTrie>::iterator> d_match_children_end;

  void reset( TermGenEnv * s, TypeNode tn );
  bool getNextTerm( TermGenEnv * s, unsigned depth );
  void resetMatching( TermGenEnv * s, TNode eqc, unsigned mode );
  bool getNextMatch( TermGenEnv * s, TNode eqc, std::map< TypeNode, std::map< unsigned, TNode > >& subs, std::map< TNode, bool >& rev_subs );

  unsigned getDepth( TermGenEnv * s );
  unsigned getGeneralizationDepth( TermGenEnv * s );
  Node getTerm( TermGenEnv * s );

  void debugPrint( TermGenEnv * s, const char * c, const char * cd );
};


class TermGenEnv
{
public:
  //collect signature information
  void collectSignatureInformation();
  //reset function
  void reset( unsigned gdepth, bool genRelevant, TypeNode tgen );
  //get next term
  bool getNextTerm();
  //reset matching
  void resetMatching( TNode eqc, unsigned mode );
  //get next match
  bool getNextMatch( TNode eqc, std::map< TypeNode, std::map< unsigned, TNode > >& subs, std::map< TNode, bool >& rev_subs );
  //get term
  Node getTerm();
  //debug print
  void debugPrint( const char * c, const char * cd );

  //conjecture generation
  ConjectureGenerator * d_cg;
  //the current number of enumerated variables per type
  std::map< TypeNode, unsigned > d_var_id;
  //the limit of number of variables per type to enumerate
  std::map< TypeNode, unsigned > d_var_limit;
  //the functions we can currently generate
  std::map< TypeNode, std::vector< TNode > > d_typ_tg_funcs;
  // whether functions must add operators
  std::map< TNode, bool > d_tg_func_param;
  //the equivalence classes (if applicable) that match the currently generated term
  bool d_gen_relevant_terms;
  //relevant equivalence classes
  std::vector< TNode > d_relevant_eqc[2];
  //candidate equivalence classes
  std::vector< std::vector< TNode > > d_ccand_eqc[2];
  //the term generation objects
  unsigned d_tg_id;
  std::map< unsigned, TermGenerator > d_tg_alloc;
  unsigned d_tg_gdepth;
  int d_tg_gdepth_limit;

  //all functions
  std::vector< TNode > d_funcs;
  //function to kind map
  std::map< TNode, Kind > d_func_kind;
  //type of each argument of the function
  std::map< TNode, std::vector< TypeNode > > d_func_args;

  //access functions
  unsigned getNumTgVars( TypeNode tn );
  bool allowVar( TypeNode tn );
  void addVar( TypeNode tn );
  void removeVar( TypeNode tn );
  unsigned getNumTgFuncs( TypeNode tn );
  TNode getTgFunc( TypeNode tn, unsigned i );
  Node getFreeVar( TypeNode tn, unsigned i );
  bool considerCurrentTerm();
  bool considerCurrentTermCanon( unsigned tg_id );
  void changeContext( bool add );
  bool isRelevantFunc( Node f );
  bool isRelevantTerm( Node t );
  //carry
  TermDb * getTermDatabase();
  Node getGroundEqc( TNode r );
  bool isGroundEqc( TNode r );
  bool isGroundTerm( TNode n );
};



class TheoremIndex
{
private:
  void addTheorem( std::vector< TNode >& lhs_v, std::vector< unsigned >& lhs_arg, TNode rhs );
  void addTheoremNode( TNode curr, std::vector< TNode >& lhs_v, std::vector< unsigned >& lhs_arg, TNode rhs );
  void getEquivalentTerms( std::vector< TNode >& n_v, std::vector< unsigned >& n_arg,
                           std::map< TNode, TNode >& smap, std::vector< TNode >& vars, std::vector< TNode >& subs,
                           std::vector< Node >& terms );
  void getEquivalentTermsNode( Node curr, std::vector< TNode >& n_v, std::vector< unsigned >& n_arg,
                               std::map< TNode, TNode >& smap, std::vector< TNode >& vars, std::vector< TNode >& subs,
                               std::vector< Node >& terms );
public:
  std::map< TypeNode, TNode > d_var;
  std::map< TNode, TheoremIndex > d_children;
  std::vector< Node > d_terms;

  void addTheorem( TNode lhs, TNode rhs ) {
    std::vector< TNode > v;
    std::vector< unsigned > a;
    addTheoremNode( lhs, v, a, rhs );
  }
  void getEquivalentTerms( TNode n, std::vector< Node >& terms ) {
    std::vector< TNode > nv;
    std::vector< unsigned > na;
    std::map< TNode, TNode > smap;
    std::vector< TNode > vars;
    std::vector< TNode > subs;
    getEquivalentTermsNode( n, nv, na, smap, vars, subs, terms );
  }
  void clear(){
    d_var.clear();
    d_children.clear();
    d_terms.clear();
  }
  void debugPrint( const char * c, unsigned ind = 0 );
};



class ConjectureGenerator : public QuantifiersModule
{
  friend class OpArgIndex;
  friend class PatGen;
  friend class PatternGenEqc;
  friend class PatternGen;
  friend class SubsEqcIndex;
  friend class TermGenerator;
  friend class TermGenEnv;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
//this class maintains a congruence closure for *universal* facts
private:
  //notification class for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    ConjectureGenerator& d_sg;
  public:
    NotifyClass(ConjectureGenerator& sg): d_sg(sg) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) override
    {
      return true;
    }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      return true;
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      return true;
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override {}
    void eqNotifyNewClass(TNode t) override { d_sg.eqNotifyNewClass(t); }
    void eqNotifyPreMerge(TNode t1, TNode t2) override
    {
      d_sg.eqNotifyPreMerge(t1, t2);
    }
    void eqNotifyPostMerge(TNode t1, TNode t2) override
    {
      d_sg.eqNotifyPostMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
      d_sg.eqNotifyDisequal(t1, t2, reason);
    }
  };/* class ConjectureGenerator::NotifyClass */
  /** The notify class */
  NotifyClass d_notify;
  class EqcInfo{
  public:
    EqcInfo( context::Context* c );
    //representative
    context::CDO< Node > d_rep;
  };
  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo( TNode n, bool doMake = false );
  /** boolean terms */
  Node d_true;
  Node d_false;
  /** (universal) equaltity engine */
  eq::EqualityEngine d_uequalityEngine;
  /** pending adds */
  std::vector< Node > d_upendingAdds;
  /** relevant terms */
  std::map< Node, bool > d_urelevant_terms;
  /** information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);
  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  /** are universal equal */
  bool areUniversalEqual( TNode n1, TNode n2 );
  /** are universal disequal */
  bool areUniversalDisequal( TNode n1, TNode n2 );
  /** get universal representative */
  Node getUniversalRepresentative(TNode n, bool add = false);
  /** set relevant */
  void setUniversalRelevant( TNode n );
  /** ordering for universal terms */
  bool isUniversalLessThan( TNode rt1, TNode rt2 );

  /** the nodes we have reported as canonical representative */
  std::vector< TNode > d_ue_canon;
  /** is reported canon */
  bool isReportedCanon( TNode n );
  /** mark that term has been reported as canonical rep */
  void markReportedCanon( TNode n );

private:  //information regarding the conjectures
  /** list of all conjectures */
  std::vector< Node > d_conjectures;
  /** list of all waiting conjectures */
  std::vector< Node > d_waiting_conjectures_lhs;
  std::vector< Node > d_waiting_conjectures_rhs;
  std::vector< int > d_waiting_conjectures_score;
  /** map of currently considered equality conjectures */
  std::map< Node, std::vector< Node > > d_waiting_conjectures;
  /** map of equality conjectures */
  std::map< Node, std::vector< Node > > d_eq_conjectures;
  /** currently existing conjectures in equality engine */
  BoolMap d_ee_conjectures;
  /** conjecture index */
  TheoremIndex d_thm_index;
private:  //free variable list
  // get canonical free variable #i of type tn
  Node getFreeVar( TypeNode tn, unsigned i );
private:  //information regarding the terms
  //relevant patterns (the LHS's)
  std::map< TypeNode, std::vector< Node > > d_rel_patterns;
  //total number of unique variables
  std::map< TNode, unsigned > d_rel_pattern_var_sum;
  //by types
  PatternTypIndex d_rel_pattern_typ_index;
  // substitution to ground EQC index
  std::map< TNode, SubstitutionIndex > d_rel_pattern_subs_index;
  //patterns (the RHS's)
  std::map< TypeNode, std::vector< Node > > d_patterns;
  //patterns to # variables per type
  std::map< TNode, std::map< TypeNode, unsigned > > d_pattern_var_id;
  // # duplicated variables
  std::map< TNode, unsigned > d_pattern_var_duplicate;
  // is normal pattern?  (variables allocated in canonical way left to right)
  std::map< TNode, int > d_pattern_is_normal;
  std::map< TNode, int > d_pattern_is_relevant;
  // patterns to a count of # operators (variables and functions)
  std::map< TNode, std::map< TNode, unsigned > > d_pattern_fun_id;
  // term size
  std::map< TNode, unsigned > d_pattern_fun_sum;
  // collect functions
  unsigned collectFunctions( TNode opat, TNode pat, std::map< TNode, unsigned >& funcs,
                             std::map< TypeNode, unsigned >& mnvn, std::map< TypeNode, unsigned >& mxvn );
  // add pattern
  void registerPattern( Node pat, TypeNode tpat );
private: //for debugging
  std::map< TNode, unsigned > d_em;
  unsigned d_conj_count;
public:
  //term generation environment
  TermGenEnv d_tge;
  //consider term canon
  bool considerTermCanon( Node ln, bool genRelevant );
public:  //for generalization
  //generalizations
  bool isGeneralization( TNode patg, TNode pat ) {
    std::map< TNode, TNode > subs;
    return isGeneralization( patg, pat, subs );
  }
  bool isGeneralization( TNode patg, TNode pat, std::map< TNode, TNode >& subs );
  // get generalization depth
  int calculateGeneralizationDepth( TNode n, std::vector< TNode >& fv );
private:
  //predicate for type
  std::map< TypeNode, Node > d_typ_pred;
  //get predicate for type
  Node getPredicateForType( TypeNode tn );
  /** get enumerate uf term
   *
   * This function adds up to #num f-applications to terms, where f is
   * n.getOperator(). These applications are enumerated in a fair manner based
   * on an iterative deepening of the sum of indices of the arguments. For
   * example, if f : U x U -> U, an the term enumerator for U gives t1, t2, t3
   * ..., then we add f-applications to terms in this order:
   *   f( t1, t1 )
   *   f( t2, t1 )
   *   f( t1, t2 )
   *   f( t1, t3 )
   *   f( t2, t2 )
   *   f( t3, t1 )
   *   ...
   * This function may add fewer than #num terms to terms if the enumeration is
   * exhausted, or if an internal error occurs.
   */
  void getEnumerateUfTerm( Node n, unsigned num, std::vector< Node >& terms );
  //
  void getEnumeratePredUfTerm( Node n, unsigned num, std::vector< Node >& terms );
  // uf operators enumerated
  std::map< Node, bool > d_uf_enum;
public:  //for property enumeration
  //process this candidate conjecture
  void processCandidateConjecture( TNode lhs, TNode rhs, unsigned lhs_depth, unsigned rhs_depth );
  //whether it should be considered, negative : no, positive returns score
  int considerCandidateConjecture( TNode lhs, TNode rhs );
  //notified of a substitution
  bool notifySubstitution( TNode glhs, std::map< TNode, TNode >& subs, TNode rhs );
  //confirmation count
  unsigned d_subs_confirmCount;
  //individual witnesses (for range)
  std::vector< TNode > d_subs_confirmWitnessRange;
  //individual witnesses (for domain)
  std::map< TNode, std::vector< TNode > > d_subs_confirmWitnessDomain;
  //number of ground substitutions whose equality is unknown
  unsigned d_subs_unkCount;
private:  //information about ground equivalence classes
  TNode d_bool_eqc[2];
  std::map< TNode, Node > d_ground_eqc_map;
  std::vector< TNode > d_ground_terms;
  //operator independent term index
  std::map< TNode, OpArgIndex > d_op_arg_index;
  //is handled term
  bool isHandledTerm( TNode n );
  Node getGroundEqc( TNode r );
  bool isGroundEqc( TNode r );
  bool isGroundTerm( TNode n );
  //has enumerated UF
  bool hasEnumeratedUf( Node n );
  // count of full effort checks
  unsigned d_fullEffortCount;
  // has added lemma
  bool d_hasAddedLemma;
  //flush the waiting conjectures
  unsigned flushWaitingConjectures( unsigned& addedLemmas, int ldepth, int rdepth );
public:
  ConjectureGenerator( QuantifiersEngine * qe, context::Context* c );
  ~ConjectureGenerator();

  /* needs check */
  bool needsCheck(Theory::Effort e) override;
  /* reset at a round */
  void reset_round(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "ConjectureGenerator"; }
  // options
 private:
  bool optReqDistinctVarPatterns();
  bool optFilterUnknown();
  int optFilterScoreThreshold();
  unsigned optFullCheckFrequency();
  unsigned optFullCheckConjectures();

  bool optStatsOnly();
};


}
}
}

#endif
