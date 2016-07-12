/*********************                                                        */
/*! \file theory_sets_rels.h
 ** \verbatim
 ** Original author: Paul Meng
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Extension to Sets theory.
 **/

#ifndef SRC_THEORY_SETS_THEORY_SETS_RELS_H_
#define SRC_THEORY_SETS_THEORY_SETS_RELS_H_

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "context/cdhashset.h"
#include "context/cdchunk_list.h"
#include "theory/sets/rels_utils.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySets;


class TupleTrie {
public:
  /** the data */
  std::map< Node, TupleTrie > d_data;
public:
  std::vector<Node> findTerms( std::vector< Node >& reps, int argIndex = 0 );
  Node existsTerm( std::vector< Node >& reps, int argIndex = 0 );
  bool addTerm( Node n, std::vector< Node >& reps, int argIndex = 0 );
  void debugPrint( const char * c, Node n, unsigned depth = 0 );
  void clear() { d_data.clear(); }
};/* class TupleTrie */

class TheorySetsRels {

  typedef context::CDChunkList<Node>                            NodeList;
  typedef context::CDChunkList<int>                             IdList;
  typedef context::CDHashMap<int, IdList*>                      IdListMap;
  typedef context::CDHashSet<Node, NodeHashFunction>            NodeSet;
  typedef context::CDHashMap<Node, bool, NodeHashFunction>      NodeBoolMap;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeListMap;
  typedef context::CDHashMap<Node, NodeSet*, NodeHashFunction>  NodeSetMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction>      NodeMap;

public:
  TheorySetsRels(context::Context* c,
                 context::UserContext* u,
                 eq::EqualityEngine*,
                 context::CDO<bool>*,
                 TheorySets&);

  ~TheorySetsRels();
  void check(Theory::Effort);
  void doPendingLemmas();

private:
  /** equivalence class info
   * d_mem tuples that are members of this equivalence class
   * d_not_mem tuples that are not members of this equivalence class
   * d_tp is a node of kind TRANSPOSE (if any) in this equivalence class,
   * d_pt is a node of kind PRODUCT (if any) in this equivalence class,
   * d_join is a node of kind JOIN (if any) in this equivalence class,
   * d_tc is a node of kind TCLOSURE (if any) in this equivalence class,
   */
  class EqcInfo
  {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    static int                  counter;
    NodeSet                     d_mem;
    NodeSet                     d_not_mem;
    NodeListMap                 d_in;
    NodeListMap                 d_out;
    NodeMap                     d_mem_exp;
    IdListMap                   d_id_in; // mapping from a element rep id to a list of rep ids that pointed by
    IdListMap                   d_id_out; // mapping from a element rep id to a list of rep ids that point to
    context::CDO< Node >        d_tp;
    context::CDO< Node >        d_pt;
    context::CDO< Node >        d_join;
    context::CDO< Node >        d_tc;
  };

private:
  std::map<int, Node>      d_id_node; // mapping between integer id and tuple element rep
  std::map<Node, int>      d_node_id; // mapping between tuple element rep and integer id

  /** has eqc info */
  bool hasEqcInfo( TNode n ) { return d_eqc_info.find( n )!=d_eqc_info.end(); }


private:
  eq::EqualityEngine            *d_eqEngine;
  context::CDO<bool>            *d_conflict;
  TheorySets&                   d_sets_theory;
  /** True and false constant nodes */
  Node                          d_trueNode;
  Node                          d_falseNode;
  // Facts and lemmas to be sent to EE
  std::map< Node, Node >        d_pending_facts;
  std::map< Node, Node >        d_pending_split_facts;
  std::vector< Node >           d_lemma_cache;
  NodeList                      d_pending_merge;
  /** inferences: maintained to ensure ref count for internally introduced nodes */
  NodeList                      d_infer;
  NodeList                      d_infer_exp;
  NodeSet                       d_lemma;
  NodeSet                       d_shared_terms;
  // tc terms that have been decomposed
  NodeSet                       d_tc_saver;

  std::hash_set< Node, NodeHashFunction >       d_rel_nodes;
  std::map< Node, std::vector<Node> >           d_tuple_reps;
  std::map< Node, TupleTrie >                   d_membership_trie;
  std::hash_set< Node, NodeHashFunction >       d_symbolic_tuples;
  std::map< Node, std::vector<Node> >           d_membership_constraints_cache;
  std::map< Node, std::vector<Node> >           d_membership_exp_cache;
  std::map< Node, std::vector<Node> >           d_membership_db;
  std::map< Node, std::vector<Node> >           d_membership_exp_db;
  std::map< Node, Node >                        d_membership_tc_exp_cache;

  std::map< Node, std::hash_set<Node, NodeHashFunction> >                       d_tc_membership_db;
  std::map< Node, std::map<kind::Kind_t, std::vector<Node> > >                  d_terms_cache;
  std::map< Node, std::map< Node, std::hash_set<Node, NodeHashFunction> > >     d_membership_tc_cache;

  /** information necessary for equivalence classes */
public:
  void eqNotifyNewClass(Node t);
  void eqNotifyPostMerge(Node t1, Node t2);

private:

  void doPendingMerge();
  std::map< Node, EqcInfo* > d_eqc_info;
  EqcInfo* getOrMakeEqcInfo( Node n, bool doMake = false );
  void mergeTransposeEqcs(Node t1, Node t2);
  void mergeProductEqcs(Node t1, Node t2);
  void mergeTCEqcs(Node t1, Node t2);
  void sendInferTranspose(bool, Node, Node, Node, bool reverseOnly = false);
  void sendInferProduct(bool, Node, Node, Node);
  void sendTCInference(EqcInfo* tc_ei, std::hash_set<int> in_reachable, std::hash_set<int> out_reachable, Node mem_rep, Node fst_rep, Node snd_rep, int id1, int id2);
  void addTCMemAndSendInfer(EqcInfo* tc_ei, Node mem, Node exp, bool fromRel = false);
  Node findTCMemExp(EqcInfo*, Node);
  void mergeTCEqcExp(EqcInfo*, EqcInfo*);
  void buildTCAndExp(Node, EqcInfo*);
  int getOrMakeElementRepId(EqcInfo*, Node);
  void collectInReachableNodes(EqcInfo* tc_ei, int start_id, std::hash_set<int>& in_reachable, bool firstRound  = true);
  void collectOutReachableNodes(EqcInfo* tc_ei, int start_id, std::hash_set<int>& out_reachable, bool firstRound  = true);
  Node explainTCMem(EqcInfo*, Node, Node, Node);


  void check();
  void collectRelsInfo();
  void assertMembership( Node fact, Node reason, bool polarity );
  void composeTupleMemForRels( Node );
  void applyTransposeRule( Node, Node, bool tp_occur_rule = false );
  void applyJoinRule( Node, Node );
  void applyProductRule( Node, Node );
  void applyTCRule( Node, Node );
  void buildTCGraph( Node, Node, Node );
  void computeRels( Node );
  void computeTransposeRelations( Node );
  void finalizeTCInfer();
  void inferTC( Node, std::map< Node, std::hash_set< Node, NodeHashFunction > >& );
  void inferTC( Node, Node, std::map< Node, std::hash_set< Node, NodeHashFunction > >&,
                Node, Node, std::hash_set< Node, NodeHashFunction >&);
  bool isTCReachable(Node fst, Node snd, std::hash_set<Node, NodeHashFunction>& hasSeen,
                      std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph);

  Node explain(Node);

  void doTCLemmas();
  void sendInfer( Node fact, Node exp, const char * c );
  void sendLemma( Node fact, Node reason, const char * c );
  void sendSplit( Node a, Node b, const char * c );
  void doPendingFacts();
  void doPendingSplitFacts();
  void addSharedTerm( TNode n );
  void checkTCGraphForConflict( Node, Node, Node, Node, Node, std::map< Node, std::hash_set< Node, NodeHashFunction > >& );

  // Helper functions
  bool insertIntoIdList(IdList&, int);
  inline Node getReason(Node tc_rep, Node tc_term, Node tc_r_rep, Node tc_r);
  inline Node constructPair(Node tc_rep, Node a, Node b);
  Node findMemExp(Node r, Node pair);
  bool safeAddToMap( std::map< Node, std::vector<Node> >&, Node, Node );
  void addToMap( std::map< Node, std::vector<Node> >&, Node, Node );
  bool hasMember( Node, Node );
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool exists( std::vector<Node>&, Node );
  bool holds( Node );
  void computeTupleReps( Node );
  void makeSharedTerm( Node );
  void reduceTupleVar( Node );
  inline void addToMembershipDB( Node, Node, Node  );
  bool isRel( Node n ) {return n.getType().isSet() && n.getType().getSetElementType().isTuple();}
  Node mkAnd( std::vector< TNode >& assumptions );
  void printNodeMap(char* fst, char* snd, NodeMap map);

};


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
