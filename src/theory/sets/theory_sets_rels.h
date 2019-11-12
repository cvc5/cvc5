/*********************                                                        */
/*! \file theory_sets_rels.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Extension to Sets theory.
 **/

#ifndef SRC_THEORY_SETS_THEORY_SETS_RELS_H_
#define SRC_THEORY_SETS_THEORY_SETS_RELS_H_

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/rels_utils.h"
#include "theory/sets/solver_state.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;

class TupleTrie {
public:
  /** the data */
  std::map< Node, TupleTrie > d_data;
public:
  std::vector<Node> findTerms( std::vector< Node >& reps, int argIndex = 0 );
  std::vector<Node> findSuccessors( std::vector< Node >& reps, int argIndex = 0 );
  Node existsTerm( std::vector< Node >& reps, int argIndex = 0 );
  bool addTerm( Node n, std::vector< Node >& reps, int argIndex = 0 );
  void debugPrint( const char * c, Node n, unsigned depth = 0 );
  void clear() { d_data.clear(); }
};/* class TupleTrie */

/** The relations extension of the theory of sets
 *
 * This class implements inference schemes described in Meng et al. CADE 2017
 * for handling quantifier-free constraints in the theory of relations.
 *
 * In CVC4, relations are represented as sets of tuples. The theory of
 * relations includes constraints over operators, e.g. TRANSPOSE, JOIN and so
 * on, which apply to sets of tuples.
 *
 * Since relations are a special case of sets, this class is implemented as an
 * extension of the theory of sets. That is, it shares many components of the
 * TheorySets object which owns it.
 */
class TheorySetsRels {
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashSet< Node, NodeHashFunction >            NodeSet;
  typedef context::CDHashMap< Node, Node, NodeHashFunction >      NodeMap;

public:
 TheorySetsRels(SolverState& s,
                InferenceManager& im,
                eq::EqualityEngine& e,
                context::UserContext* u);

 ~TheorySetsRels();
 /**
  * Invoke the check method with effort level e. At a high level, this class
  * will make calls to TheorySetsPrivate::processInference to assert facts,
  * lemmas, and conflicts. If this class makes no such call, then the current
  * set of assertions is satisfiable with respect to relations.
  */
 void check(Theory::Effort e);
 /** Is kind k a kind that belongs to the relation theory? */
 static bool isRelationKind(Kind k);

private:
  /** True and false constant nodes */
  Node                          d_trueNode;
  Node                          d_falseNode;

  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** A list of pending inferences to process */
  std::vector<Node> d_pending;
  NodeSet                       d_shared_terms;


  std::unordered_set< Node, NodeHashFunction >       d_rel_nodes;
  std::map< Node, std::vector<Node> >           d_tuple_reps;
  std::map< Node, TupleTrie >                   d_membership_trie;

  /** Symbolic tuple variables that has been reduced to concrete ones */
  std::unordered_set< Node, NodeHashFunction >       d_symbolic_tuples;

  /** Mapping between relation and its member representatives */
  std::map< Node, std::vector< Node > >           d_rReps_memberReps_cache;

  /** Mapping between relation and its member representatives explanation */
  std::map< Node, std::vector< Node > >           d_rReps_memberReps_exp_cache;

  /** Mapping between a relation representative and its equivalent relations involving relational operators */
  std::map< Node, std::map<kind::Kind_t, std::vector<Node> > >                  d_terms_cache;

  /** Mapping between transitive closure relation TC(r) and its TC graph constructed based on the members of r*/
  std::map< Node, std::map< Node, std::unordered_set<Node, NodeHashFunction> > >     d_rRep_tcGraph;
  std::map< Node, std::map< Node, std::unordered_set<Node, NodeHashFunction> > >     d_tcr_tcGraph;
  std::map< Node, std::map< Node, Node > > d_tcr_tcGraph_exps;

 private:
  /** Send infer
   *
   * Called when we have inferred fact from explanation reason, where the
   * latter should be a conjunction of facts that hold in the current context.
   *
   * The argument c is used for debugging, to give the name of the inference
   * rule being used.
   *
   * This method adds the node (=> reason exp) to the pending vector d_pending.
   */
  void sendInfer(Node fact, Node reason, const char* c);
  /**
   * This method flushes the inferences in the pending vector d_pending to
   * theory of sets, which may process them as lemmas or as facts to assert to
   * the equality engine.
   */
  void doPendingInfers();
  /** Process inference
   *
   * A wrapper around d_im.assertInference that ensures that we do not send
   * inferences with explanations that are not entailed.
   *
   * Argument c is used for debugging, typically the name of the inference.
   */
  void processInference(Node conc, Node exp, const char* c);

  /** Methods used in full effort */
  void check();
  void collectRelsInfo();
  void applyTransposeRule( std::vector<Node> tp_terms );
  void applyTransposeRule( Node rel, Node rel_rep, Node exp );
  void applyProductRule( Node rel, Node rel_rep, Node exp );
  void applyJoinRule( Node rel, Node rel_rep, Node exp);
  void applyJoinImageRule( Node mem_rep, Node rel_rep, Node exp);
  void applyIdenRule( Node mem_rep, Node rel_rep, Node exp);
  void applyTCRule( Node mem, Node rel, Node rel_rep, Node exp);
  void buildTCGraphForRel( Node tc_rel );
  void doTCInference();
  void doTCInference( std::map< Node, std::unordered_set<Node, NodeHashFunction> > rel_tc_graph, std::map< Node, Node > rel_tc_graph_exps, Node tc_rel );
  void doTCInference(Node tc_rel, std::vector< Node > reasons, std::map< Node, std::unordered_set< Node, NodeHashFunction > >& tc_graph,
                       std::map< Node, Node >& rel_tc_graph_exps, Node start_node_rep, Node cur_node_rep, std::unordered_set< Node, NodeHashFunction >& seen );

  void composeMembersForRels( Node );
  void computeMembersForBinOpRel( Node );
  void computeMembersForIdenTerm( Node );
  void computeMembersForUnaryOpRel( Node );
  void computeMembersForJoinImageTerm( Node );

  bool isTCReachable( Node mem_rep, Node tc_rel );
  void isTCReachable( Node start, Node dest, std::unordered_set<Node, NodeHashFunction>& hasSeen,
                    std::map< Node, std::unordered_set< Node, NodeHashFunction > >& tc_graph, bool& isReachable );

  /** Helper functions */
  bool hasTerm( Node a );
  void makeSharedTerm( Node );
  void reduceTupleVar( Node );
  bool hasMember( Node, Node );
  void computeTupleReps( Node );
  bool areEqual( Node a, Node b );
  Node getRepresentative( Node t );
  inline void addToMembershipDB( Node, Node, Node  );
  inline Node constructPair(Node tc_rep, Node a, Node b);
  bool safelyAddToMap( std::map< Node, std::vector<Node> >&, Node, Node );
  bool isRel( Node n ) {return n.getType().isSet() && n.getType().getSetElementType().isTuple();}
};


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
