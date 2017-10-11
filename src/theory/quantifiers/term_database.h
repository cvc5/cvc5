/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include <map>
#include <unordered_set>

#include "expr/attribute.h"
#include "theory/theory.h"
#include "theory/type_enumerator.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst{
  class Trigger;
  class HigherOrderTrigger;
}

namespace quantifiers {

class TermArgTrie {
public:
  /** the data */
  std::map< TNode, TermArgTrie > d_data;
public:
  bool hasNodeData() { return !d_data.empty(); }
  TNode getNodeData() { return d_data.begin()->first; }
  TNode existsTerm( std::vector< TNode >& reps, int argIndex = 0 );
  TNode addOrGetTerm( TNode n, std::vector< TNode >& reps, int argIndex = 0 );
  bool addTerm( TNode n, std::vector< TNode >& reps, int argIndex = 0 );
  void debugPrint( const char * c, Node n, unsigned depth = 0 );
  void clear() { d_data.clear(); }
};/* class TermArgTrie */

namespace fmcheck {
  class FullModelChecker;
}

class TermDbSygus;
class QuantConflictFind;
class RelevantDomain;
class ConjectureGenerator;
class TermGenerator;
class TermGenEnv;

class TermDb : public QuantifiersUtil {
  friend class ::CVC4::theory::QuantifiersEngine;
  //TODO: eliminate most of these
  friend class ::CVC4::theory::inst::Trigger;
  friend class ::CVC4::theory::inst::HigherOrderTrigger;
  friend class ::CVC4::theory::quantifiers::fmcheck::FullModelChecker;
  friend class ::CVC4::theory::quantifiers::QuantConflictFind;
  friend class ::CVC4::theory::quantifiers::RelevantDomain;
  friend class ::CVC4::theory::quantifiers::ConjectureGenerator;
  friend class ::CVC4::theory::quantifiers::TermGenEnv;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** terms processed */
  std::unordered_set< Node, NodeHashFunction > d_processed;
  /** terms processed */
  std::unordered_set< Node, NodeHashFunction > d_iclosure_processed;
  /** select op map */
  std::map< Node, std::map< TypeNode, Node > > d_par_op_map;
  /** whether master equality engine is UF-inconsistent */
  bool d_consistent_ee;
  /** boolean terms */
  Node d_true;
  Node d_false;
public:
  TermDb(context::Context* c, context::UserContext* u, QuantifiersEngine* qe);
  ~TermDb();
  
  /** register quantified formula */
  void registerQuantifier( Node q );
public:
  /** presolve (called once per user check-sat) */
  void presolve();
  /** reset (calculate which terms are active) */
  bool reset( Theory::Effort effort );
  /** identify */
  std::string identify() const { return "TermDb"; }  
private:
  /** map from operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** inactive map */
  NodeBoolMap d_inactive_map;

  /** count number of non-redundant ground terms per operator */
  std::map< Node, int > d_op_nonred_count;
  /**mapping from UF terms to representatives of their arguments */
  std::map< TNode, std::vector< TNode > > d_arg_reps;
  /** map from operators to trie */
  std::map< Node, TermArgTrie > d_func_map_trie;
  std::map< Node, TermArgTrie > d_func_map_eqc_trie;
  /** mapping from operators to their representative relevant domains */
  std::map< Node, std::map< unsigned, std::vector< Node > > > d_func_map_rel_dom;
  /** has map */
  std::map< Node, bool > d_has_map;
  /** map from reps to a term in eqc in d_has_map */
  std::map< Node, Node > d_term_elig_eqc;  
  /** set has term */
  void setHasTerm( Node n );
  /** evaluate term */
  Node evaluateTerm2( TNode n, std::map< TNode, Node >& visited, EqualityQuery * qy, bool useEntailmentTests );
  TNode getEntailedTerm2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, EqualityQuery * qy );
  bool isEntailed2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, bool pol, EqualityQuery * qy );
  /** compute uf eqc terms */
  void computeUfEqcTerms( TNode f );
  /** compute uf terms */
  void computeUfTerms( TNode f );
private: // for higher-order term indexing
  /** a map from matchable operators to their representative */
  std::map< TNode, TNode > d_ho_op_rep;
  /** for each representative matchable operator, the list of other matchable operators in their equivalence class */
  std::map< TNode, std::vector< TNode > > d_ho_op_rep_slaves;
  /** get operator representative */
  Node getOperatorRepresentative( TNode op ) const;
public:
  /** ground terms for operator */
  unsigned getNumGroundTerms( Node f );
  /** get ground term for operator */
  Node getGroundTerm( Node f, unsigned i );
  /** get num type terms */
  unsigned getNumTypeGroundTerms( TypeNode tn );
  /** get type ground term */
  Node getTypeGroundTerm( TypeNode tn, unsigned i );
  /** add a term to the database */
  void addTerm( Node n, std::set< Node >& added, bool withinQuant = false, bool withinInstClosure = false );
  /** get match operator */
  Node getMatchOperator( Node n );
  /** get term arg index */
  TermArgTrie * getTermArgTrie( Node f );
  TermArgTrie * getTermArgTrie( Node eqc, Node f );
  /** exists term */
  TNode getCongruentTerm( Node f, Node n );
  TNode getCongruentTerm( Node f, std::vector< TNode >& args );
  /** compute arg reps */
  void computeArgReps( TNode n );
  /** in relevant domain */
  bool inRelevantDomain( TNode f, unsigned i, TNode r );
  /** evaluate a term under a substitution.  Return representative in EE if possible.
   * subsRep is whether subs contains only representatives
   */
  Node evaluateTerm( TNode n, EqualityQuery * qy = NULL, bool useEntailmentTests = false );
  /** get entailed term, does not construct new terms, less aggressive */
  TNode getEntailedTerm( TNode n, EqualityQuery * qy = NULL );
  TNode getEntailedTerm( TNode n, std::map< TNode, TNode >& subs, bool subsRep, EqualityQuery * qy = NULL );
  /** is entailed (incomplete check) */
  bool isEntailed( TNode n, bool pol, EqualityQuery * qy = NULL );
  bool isEntailed( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool pol, EqualityQuery * qy = NULL );
  /** is active */
  bool isTermActive( Node n );
  void setTermInactive( Node n );
  /** has term */
  bool hasTermCurrent( Node n, bool useMode = true );
  /** is term eligble for instantiation? */
  bool isTermEligibleForInstantiation( TNode n, TNode f, bool print = false );
  /** get has term eqc */
  Node getEligibleTermInEqc( TNode r );
  /** is inst closure */
  bool isInstClosure( Node r );
  
//for model basis
private:
  //map from types to model basis terms
  std::map< TypeNode, Node > d_model_basis_term;
  //map from ops to model basis terms
  std::map< Node, Node > d_model_basis_op_term;
  //map from instantiation terms to their model basis equivalent
  std::map< Node, Node > d_model_basis_body;
  /** map from universal quantifiers to model basis terms */
  std::map< Node, std::vector< Node > > d_model_basis_terms;
  // compute model basis arg
  void computeModelBasisArgAttribute( Node n );
public:
  //get model basis term
  Node getModelBasisTerm( TypeNode tn, int i = 0 );
  //get model basis term for op
  Node getModelBasisOpTerm( Node op );
  //get model basis
  Node getModelBasis( Node q, Node n );
  //get model basis body
  Node getModelBasisBody( Node q );
  
};/* class TermDb */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */
