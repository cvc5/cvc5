/*********************                                                        */
/*! \file quant_conflict_find.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifiers conflict find class
 **/

#include "cvc4_private.h"

#ifndef QUANT_CONFLICT_FIND
#define QUANT_CONFLICT_FIND

#include <ostream>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node_trie.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantConflictFind;
class QuantInfo;

//match generator
class MatchGen {
  friend class QuantInfo;
private:
  //current children information
  int d_child_counter;
  bool d_use_children;
  //children of this object
  std::vector< int > d_children_order;
  unsigned getNumChildren() { return d_children.size(); }
  MatchGen * getChild( int i ) { return &d_children[d_children_order[i]]; }
  //MatchGen * getChild( int i ) { return &d_children[i]; }
  //current matching information
  std::vector<TNodeTrie*> d_qn;
  std::vector<std::map<TNode, TNodeTrie>::iterator> d_qni;
  bool doMatching( QuantConflictFind * p, QuantInfo * qi );
  //for matching : each index is either a variable or a ground term
  unsigned d_qni_size;
  std::map< int, int > d_qni_var_num;
  std::map< int, TNode > d_qni_gterm;
  std::map< int, int > d_qni_bound;
  std::vector< int > d_qni_bound_except;
  std::map< int, TNode > d_qni_bound_cons;
  std::map< int, int > d_qni_bound_cons_var;
  std::map< int, int >::iterator d_binding_it;
  //std::vector< int > d_independent;
  bool d_matched_basis;
  bool d_binding;
  //int getVarBindingVar();
  std::map< int, Node > d_ground_eval;
  //determine variable order
  void determineVariableOrder( QuantInfo * qi, std::vector< int >& bvars );
  void collectBoundVar( QuantInfo * qi, Node n, std::vector< int >& cbvars, std::map< Node, bool >& visited, bool& hasNested );
public:
  //type of the match generator
  enum {
    typ_invalid,
    typ_ground,
    typ_pred,
    typ_eq,
    typ_formula,
    typ_var,
    typ_bool_var,
    typ_tconstraint,
    typ_tsym,
  };
  void debugPrintType( const char * c, short typ, bool isTrace = false );
public:
  MatchGen();
  MatchGen( QuantInfo * qi, Node n, bool isVar = false );
  bool d_tgt;
  bool d_tgt_orig;
  bool d_wasSet;
  Node d_n;
  std::vector< MatchGen > d_children;
  short d_type;
  bool d_type_not;
  /** reset round
   *
   * Called once at the beginning of each full/last-call effort, prior to
   * processing this match generator. This method returns false if the reset
   * failed, e.g. if a conflict was encountered during term indexing.
   */
  bool reset_round(QuantConflictFind* p);
  void reset( QuantConflictFind * p, bool tgt, QuantInfo * qi );
  bool getNextMatch( QuantConflictFind * p, QuantInfo * qi );
  bool isValid() { return d_type!=typ_invalid; }
  void setInvalid();

  // is this term treated as UF application?
  static bool isHandledBoolConnective( TNode n );
  static bool isHandledUfTerm( TNode n );
  static Node getMatchOperator( QuantConflictFind * p, Node n );
  //can this node be handled by the algorithm
  static bool isHandled( TNode n );
};

//info for quantifiers
class QuantInfo {
private:
  void registerNode( Node n, bool hasPol, bool pol, bool beneathQuant = false );
  void flatten( Node n, bool beneathQuant );
private: //for completing match
  std::vector< int > d_unassigned;
  std::vector< TypeNode > d_unassigned_tn;
  int d_unassigned_nvar;
  int d_una_index;
  std::vector< int > d_una_eqc_count;
  //optimization: track which arguments variables appear under UF terms in
  std::map< int, std::map< TNode, std::vector< unsigned > > > d_var_rel_dom;
  void getPropagateVars( QuantConflictFind * p, std::vector< TNode >& vars, TNode n, bool pol, std::map< TNode, bool >& visited );
  //optimization: number of variables set, to track when we can stop
  std::map< int, bool > d_vars_set;
  std::vector< Node > d_extra_var;
public:
  bool isBaseMatchComplete();
public:
  QuantInfo();
  ~QuantInfo();
  std::vector< TNode > d_vars;
  std::vector< TypeNode > d_var_types;
  std::map< TNode, int > d_var_num;
  std::vector< int > d_tsym_vars;
  std::map< TNode, bool > d_inMatchConstraint;
  int getVarNum( TNode v ) { return d_var_num.find( v )!=d_var_num.end() ? d_var_num[v] : -1; }
  bool isVar( TNode v ) { return d_var_num.find( v )!=d_var_num.end(); }
  int getNumVars() { return (int)d_vars.size(); }
  TNode getVar( int i ) { return d_vars[i]; }

  typedef std::map< int, MatchGen * > VarMgMap;
 private:
  MatchGen * d_mg;
  VarMgMap d_var_mg;
 public:
  VarMgMap::const_iterator var_mg_find(int i) const { return d_var_mg.find(i); }
  VarMgMap::const_iterator var_mg_end() const { return d_var_mg.end(); }
  bool containsVarMg(int i) const { return var_mg_find(i) != var_mg_end(); }

  bool matchGeneratorIsValid() const { return d_mg->isValid(); }
  bool getNextMatch( QuantConflictFind * p ) {
    return d_mg->getNextMatch(p, this);
  }

  Node d_q;
  bool reset_round( QuantConflictFind * p );
public:
  //initialize
  void initialize( QuantConflictFind * p, Node q, Node qn );
  //current constraints
  std::vector< TNode > d_match;
  std::vector< TNode > d_match_term;
  std::map< int, std::map< TNode, int > > d_curr_var_deq;
  std::map< Node, bool > d_tconstraints;
  int getCurrentRepVar( int v );
  TNode getCurrentValue( TNode n );
  TNode getCurrentExpValue( TNode n );
  bool getCurrentCanBeEqual( QuantConflictFind * p, int v, TNode n, bool chDiseq = false );
  int addConstraint( QuantConflictFind * p, int v, TNode n, bool polarity );
  int addConstraint( QuantConflictFind * p, int v, TNode n, int vn, bool polarity, bool doRemove );
  bool setMatch( QuantConflictFind * p, int v, TNode n, bool isGroundRep, bool isGround );
  void unsetMatch( QuantConflictFind * p, int v );
  bool isMatchSpurious( QuantConflictFind * p );
  bool isTConstraintSpurious( QuantConflictFind * p, std::vector< Node >& terms );
  bool entailmentTest( QuantConflictFind * p, Node lit, bool chEnt = true );
  bool completeMatch( QuantConflictFind * p, std::vector< int >& assigned, bool doContinue = false );
  void revertMatch( QuantConflictFind * p, std::vector< int >& assigned );
  void debugPrintMatch( const char * c );
  bool isConstrainedVar( int v );
public:
  void getMatch( std::vector< Node >& terms );
};

class QuantConflictFind : public QuantifiersModule
{
  friend class MatchGen;
  friend class QuantInfo;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  context::CDO< bool > d_conflict;
  std::map< Kind, Node > d_zero;
  //for storing nodes created during t-constraint solving (prevents memory leaks)
  std::vector< Node > d_tempCache;
  //optimization: list of quantifiers that depend on ground function applications
  std::map< TNode, std::vector< Node > > d_func_rel_dom;
  std::map< TNode, bool > d_irr_func;
  std::map< Node, bool > d_irr_quant;
  void setIrrelevantFunction( TNode f );
private:
  std::map< Node, Node > d_op_node;
  std::map< Node, int > d_fid;
public:  //for ground terms
  Node d_true;
  Node d_false;
  TNode getZero( Kind k );
private:
  std::map< Node, QuantInfo > d_qinfo;
private:  //for equivalence classes
  // type -> list(eqc)
  std::map< TypeNode, std::vector< TNode > > d_eqcs;

 public:
  enum Effort : unsigned {
    EFFORT_CONFLICT,
    EFFORT_PROP_EQ,
    EFFORT_INVALID,
  };
  void setEffort(Effort e) { d_effort = e; }

  inline bool atConflictEffort() const {
    return d_effort == QuantConflictFind::EFFORT_CONFLICT;
  }

 private:
  Effort d_effort;

 public:
  bool areMatchEqual( TNode n1, TNode n2 );
  bool areMatchDisequal( TNode n1, TNode n2 );
public:
  QuantConflictFind( QuantifiersEngine * qe, context::Context* c );

  /** register quantifier */
  void registerQuantifier(Node q) override;

 public:
  /** needs check */
  bool needsCheck(Theory::Effort level) override;
  /** reset round */
  void reset_round(Theory::Effort level) override;
  /** check
   *
   * This method attempts to construct a conflicting or propagating instance.
   * If such an instance exists, then it makes a call to
   * Instantiation::addInstantiation or QuantifiersEngine::addLemma.
   */
  void check(Theory::Effort level, QEffort quant_e) override;

 private:
  /** check quantified formula
   *
   * This method is called by the above check method for each quantified
   * formula q. It attempts to find a conflicting or propagating instance for
   * q, depending on the effort level (d_effort).
   *
   * isConflict: this is set to true if we discovered a conflicting instance.
   * This flag may be set instead of d_conflict if --qcf-all-conflict is true,
   * in which we continuing adding all conflicts.
   * addedLemmas: tracks the total number of lemmas added, and is incremented by
   * this method when applicable.
   */
  void checkQuantifiedFormula(Node q, bool& isConflict, unsigned& addedLemmas);

 private:
  void debugPrint( const char * c );
  //for debugging
  std::vector< Node > d_quants;
  std::map< Node, int > d_quant_id;
  void debugPrintQuant( const char * c, Node q );
  void debugPrintQuantBody( const char * c, Node q, Node n, bool doVarNum = true );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_inst_rounds;
    IntStat d_entailment_checks;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  /** Identify this module */
  std::string identify() const override { return "QcfEngine"; }
  /** is n a propagating instance?
   *
   * A propagating instance is any formula that consists of Boolean connectives,
   * equality, quantified formulas, and terms that exist in the current
   * context (those in the master equality engine).
   *
   * Notice the distinction that quantified formulas that do not appear in the
   * current context are considered to be legal in propagating instances. This
   * choice is significant for TPTP, where a net of ~200 benchmarks are gained
   * due to this decision.
   *
   * Propagating instances are the second most useful kind of instantiation
   * after conflicting instances and are used as a second effort in the
   * algorithm performed by this class.
   */
  bool isPropagatingInstance(Node n) const;
};

std::ostream& operator<<(std::ostream& os, const QuantConflictFind::Effort& e);

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
