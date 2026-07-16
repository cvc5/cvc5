/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extension to Sets theory.
 */

#ifndef SRC_THEORY_SETS_THEORY_SETS_RELS_H_
#define SRC_THEORY_SETS_THEORY_SETS_RELS_H_

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/rels_utils.h"
#include "theory/sets/solver_state.h"
#include "theory/sets/term_registry.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

class TheorySetsPrivate;

/**
 * A prefix tree for tuples and their elements' representatives.
 * Suppose we have a tuple representative t = <e1, ..., en>,
 * then the tuple tree would be
 * e1 -> e2 -> ... -> e_n -> t
 */
class TupleTrie
{
 public:
  /** the data */
  std::map<Node, TupleTrie> d_data;

 public:
  std::vector<Node> findTerms(std::vector<Node>& reps, int argIndex = 0);
  std::vector<Node> findSuccessors(std::vector<Node>& reps, int argIndex = 0);
  Node existsTerm(std::vector<Node>& reps, int argIndex = 0);
  bool addTerm(Node n, std::vector<Node>& reps, int argIndex = 0);
  void debugPrint(const char* c, Node n, unsigned depth = 0);
  void clear() { d_data.clear(); }
}; /* class TupleTrie */

/** The relations extension of the theory of sets
 *
 * This class implements inference schemes described in Meng et al. CADE 2017
 * for handling quantifier-free constraints in the theory of relations.
 *
 * In cvc5, relations are represented as sets of tuples. The theory of
 * relations includes constraints over operators, e.g. RELATION_TRANSPOSE,
 * RELATION_JOIN and so on, which apply to sets of tuples.
 *
 * Since relations are a special case of sets, this class is implemented as an
 * extension of the theory of sets. That is, it shares many components of the
 * TheorySets object which owns it.
 */
class TheorySetsRels : protected EnvObj
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, Node> NodeMap;

 public:
  TheorySetsRels(Env& env,
                 SolverState& s,
                 InferenceManager& im,
                 SkolemCache& skc,
                 TermRegistry& treg);

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
  Node d_trueNode;
  Node d_falseNode;

  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the skolem cache */
  SkolemCache& d_skCache;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  NodeSet d_shared_terms;

  std::unordered_set<Node> d_rel_nodes;
  /** a map from tuples to their elements' representatives*/
  std::map<Node, std::vector<Node> > d_tuple_reps;
  /** a map from relation terms to their member tuples*/
  std::map<Node, TupleTrie> d_membership_trie;

  /** Symbolic tuple variables that has been reduced to concrete ones */
  std::unordered_set<Node> d_symbolic_tuples;

  /** Mapping between relation and its member representatives */
  std::map<Node, std::vector<Node> > d_rReps_memberReps_cache;

  /** Mapping between relation and its member representatives explanation */
  std::map<Node, std::vector<Node> > d_rReps_memberReps_exp_cache;

  /** Mapping between a relation representative and its equivalent relations
   * involving relational operators */
  std::map<Node, std::map<Kind, std::vector<Node> > > d_terms_cache;

  /**
   * Transitive closure (TC) graphs.
   *
   * For a term (rel.tclosure r), we maintain a "TC graph": an adjacency-list
   * representation of the known members of a binary relation, i.e. a map
   * from element representative a to the set of element representatives b
   * such that the pair (a, b) is currently asserted to be a member. These
   * graphs are built lazily during a full-effort check (see
   * buildTCGraphForRel) and cleared at the end of each such check; they are
   * caches for a single call to check(Theory::Effort), not context-dependent
   * data structures.
   */
  /**
   * Mapping between the representative of a base relation r (the argument of a
   * rel.tclosure term) and the TC graph induced by the asserted members of r
   * only. Used by isTCReachable to recognize memberships of TC(r) that are
   * already derivable from the members of r, in which case applyTCRule
   * skips sending a redundant lemma. Also serves as a "graph already built"
   * marker: check() and applyTCRule test this map before calling
   * buildTCGraphForRel, which protects the entries in d_tcr_tcGraph from
   * being overwritten (buildTCGraphForRel would discard the edges that
   * applyTCRule has added there in the meantime).
   */
  std::map<Node, std::map<Node, std::unordered_set<Node> > > d_rRep_tcGraph;
  /**
   * Mapping between a transitive closure term TC(r) = (rel.tclosure r) and its
   * TC graph. Seeded by buildTCGraphForRel with the edges of d_rRep_tcGraph for
   * r's representative, and extended by applyTCRule with pairs that are
   * asserted to be members of TC(r) directly (and are not already reachable in
   * the base graph). At the end of a full-effort check, doTCInference() closes
   * each of these graphs transitively and infers the implied memberships.
   */
  std::map<Node, std::map<Node, std::unordered_set<Node> > > d_tcr_tcGraph;
  /**
   * Maps a transitive closure term TC(r) to the explanations of the edges in
   * its TC graph. Each edge (a, b) is keyed by the pair tuple
   * RelsUtils::constructPair(TC(r), a, b) built from the endpoint
   * representatives, and maps to the membership assertion that justifies the
   * edge. doTCInference conjoins these explanations along a path to form the
   * reason for each inferred membership.
   */
  std::map<Node, std::map<Node, Node> > d_tcr_tcGraph_exps;

 private:
  /** Send infer
   *
   * Called when we have inferred fact from explanation reason, where the
   * latter should be a conjunction of facts that hold in the current context.
   *
   * This method adds the node (=> reason exp) to the pending vector d_pending.
   */
  void sendInfer(Node fact, InferenceId id, Node reason);
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
   */
  void processInference(Node conc, InferenceId id, Node exp);

  /** Methods used in full effort */
  void check();
  void collectRelsInfo();
  void applyTransposeRule(std::vector<Node> tp_terms);
  void applyTransposeRule(Node rel, Node rel_rep, Node exp);
  void applyProductRule(Node rel, Node rel_rep, Node exp);
  void applyJoinRule(Node rel, Node rel_rep, Node exp);
  /**
   * @param n is a ((_ table.join m1 n1 ... mk nk) A B) where A, B are tables
   * @param nRep a representative of n
   * @param exp a membership constraint of the form (set.member e n)
   *        where e is an element of the form (tuple a1 ... am b1 ... bn)
   * This function sends a fact that represents the following
   * (=>
   *   (set.member e n)
   *   (and
   *     (= a_{m1} b_{n1}) ... (= a_{mk} b_{nk})
   *     (set.member (tuple a1 ... am) A)
   *     (set.member (tuple b1 ... bn) B)))
   */
  void applyTableJoinRule(Node n, Node nRep, Node exp);
  void applyJoinImageRule(Node mem_rep, Node rel_rep, Node exp);
  void applyIdenRule(Node mem_rep, Node rel_rep, Node exp);
  /**
   * Process a membership in a transitive closure term.
   *
   * @param mem a tuple (a, b) asserted to be a member of rel_rep
   * @param rel a term TC(r) = (rel.tclosure r) occurring in the equivalence
   *        class of rel_rep
   * @param rel_rep the representative of rel
   * @param exp the explanation of the membership, of the form
   *        (set.member mem s) where s is equal to rel
   *
   * If the membership is already derivable from the members of r (see
   * isTCReachable), this method does nothing. Otherwise it records the edge
   * (a, b) and its explanation in d_tcr_tcGraph / d_tcr_tcGraph_exps, and
   * sends the lemma that unfolds the closure one step
   * (InferenceId::SETS_RELS_TCLOSURE_UP):
   *   (set.member (a, b) TC(r)) =>
   *     (set.member (a, b) r)
   *     or ((set.member (a, z1) r) and (set.member (z2, b) r)
   *         and (z1 = z2 or (set.member (z1, z2) TC(r))))
   * where z1, z2 are skolems for the intermediate nodes on the path
   * from a to b.
   */
  void applyTCRule(Node mem, Node rel, Node rel_rep, Node exp);
  /**
   * Construct the (partial) TC graph for tc_rel = (rel.tclosure r) from the
   * currently asserted members of r, with all nodes and edges expressed in
   * terms of representatives. If r has at least one member, the graph is stored
   * in d_rRep_tcGraph (keyed by r's representative) and in d_tcr_tcGraph /
   * d_tcr_tcGraph_exps (keyed by tc_rel), overwriting any existing entries;
   * callers must check d_rRep_tcGraph and d_rel_nodes first so that edges
   * previously added to d_tcr_tcGraph by applyTCRule are not lost.
   */
  void buildTCGraphForRel(Node tc_rel);
  /**
   * Called at the end of a full-effort check. For each transitive closure
   * term TC(r) with a graph in d_tcr_tcGraph, computes the transitive
   * closure of that graph and infers all implied memberships
   * (InferenceId::SETS_RELS_TCLOSURE_FWD) via the overload below.
   */
  void doTCInference();
  /**
   * Infer all memberships implied by the TC graph rel_tc_graph of the
   * transitive closure term tc_rel: for each edge, start a depth-first
   * traversal (the recursive overload below) that derives a membership in
   * tc_rel for every node reachable from the edge's source.
   * rel_tc_graph_exps maps each edge of the graph to its explanation, as in
   * d_tcr_tcGraph_exps.
   */
  void doTCInference(std::map<Node, std::unordered_set<Node> > rel_tc_graph,
                     std::map<Node, Node> rel_tc_graph_exps,
                     Node tc_rel);
  /**
   * Recursive step of the traversal above, having reached cur_node_rep from
   * start_node_rep. reasons holds the explanations of the edges along the
   * current path; this method sends the inference that the pair (start of
   * path, end of path) is a member of tc_rel, whose reason is the
   * conjunction of reasons together with the equalities connecting adjacent
   * path edges and connecting each explanation's relation term to tc_rel's
   * base relation. It then recurses into the successors of cur_node_rep that
   * are not in seen, the set of already-traversed nodes used to terminate on
   * cycles.
   */
  void doTCInference(Node tc_rel,
                     std::vector<Node> reasons,
                     std::map<Node, std::unordered_set<Node> >& tc_graph,
                     std::map<Node, Node>& rel_tc_graph_exps,
                     Node start_node_rep,
                     Node cur_node_rep,
                     std::unordered_set<Node>& seen);

  void composeMembersForRels(Node);
  /**
   * @param n is ((_ rel.join m1 n1 ... mk nk) A B) where A, B are relations
   * This functions looks for current members of A, B.
   * For each pair e1 = (tuple a1 ... am) in A, e2 = (tuple b1 ... bn) in B
   * this function sends the following fact
   *  (=>
   *    (and
   *      (set.member e1 A)
   *      (set.member e2 B)
   *      (= a_{m1} b_{n1}) ... (= a_{mk} b_{nk}))
   *    (set.member (tuple a1 ... am b1 ... bn) n))
   */
  void applyTableJoinUp(Node);
  void computeMembersForBinOpRel(Node);
  void computeMembersForIdenTerm(Node);
  void computeMembersForUnaryOpRel(Node);
  void computeMembersForJoinImageTerm(Node);

  /**
   * Is the membership of pair mem_rep in tc_rel = (rel.tclosure r) already
   * derivable from the asserted members of r? Returns true if mem_rep is a
   * known member of r's representative, or if the second element of mem_rep
   * is reachable from its first element in the TC graph stored in
   * d_rRep_tcGraph for r. Used by applyTCRule to avoid sending redundant
   * lemmas.
   */
  bool isTCReachable(Node mem_rep, Node tc_rel);
  /**
   * Recursive helper for the above: depth-first search in tc_graph, setting
   * isReachable to true if dest can be reached from start. hasSeen is the
   * set of already-visited nodes, used to terminate on cycles.
   */
  void isTCReachable(Node start,
                     Node dest,
                     std::unordered_set<Node>& hasSeen,
                     std::map<Node, std::unordered_set<Node> >& tc_graph,
                     bool& isReachable);

  /** Helper functions */
  bool hasTerm(Node a);
  void makeSharedTerm(Node a);
  void reduceTupleVar(Node);
  bool hasMember(Node, Node);
  void computeTupleReps(Node);
  bool areEqual(Node a, Node b);
  Node getRepresentative(Node t);
  inline void addToMembershipDB(Node, Node, Node);
  inline Node constructPair(Node tc_rep, Node a, Node b);
  bool safelyAddToMap(std::map<Node, std::vector<Node> >&, Node, Node);
  bool isRel(Node n)
  {
    return n.getType().isSet() && n.getType().getSetElementType().isTuple();
  }
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
