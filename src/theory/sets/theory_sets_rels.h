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

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySets;


class TupleTrie {
public:
  /** the data */
  std::map< Node, TupleTrie > d_data;
public:
  std::vector<Node> existsTerm( std::vector< Node >& reps, int argIndex = 0 );
  bool addTerm( Node n, std::vector< Node >& reps, int argIndex = 0 );
  void debugPrint( const char * c, Node n, unsigned depth = 0 );
  void clear() { d_data.clear(); }
};/* class TupleTrie */

class TheorySetsRels {

  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

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

  TheorySets& d_sets;

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  // Facts and lemmas to be sent to EE
  std::map< Node, Node > d_pending_facts;
  std::map< Node, Node > d_pending_split_facts;
  std::vector< Node > d_lemma_cache;

  /** inferences: maintained to ensure ref count for internally introduced nodes */
  NodeList d_infer;
  NodeList d_infer_exp;
  NodeList d_lemma;

  std::map< Node, std::vector<Node> > d_tuple_reps;
  std::map< Node, TupleTrie > d_membership_trie;
  std::hash_set< Node, NodeHashFunction > d_shared_terms;
  std::hash_set< Node, NodeHashFunction > d_symbolic_tuples;
  std::map< Node, std::vector<Node> > d_membership_cache;
  std::map< Node, std::vector<Node> > d_membership_db;
  std::map< Node, std::vector<Node> > d_membership_exp_cache;
  std::map< Node, std::map<kind::Kind_t, std::vector<Node> > > d_terms_cache;

  eq::EqualityEngine *d_eqEngine;
  context::CDO<bool> *d_conflict;

  void check();
  void collectRelsInfo();
  void assertMembership( Node fact, Node reason, bool polarity );
  void composeTuplesForRels( Node );
  void applyTransposeRule( Node, Node, Node );
  void applyJoinRule( Node, Node, Node );
  void applyProductRule( Node, Node, Node );
  void computeRels( Node );
  void computeTransposeRelations( Node );
  Node reverseTuple( Node );

  void sendInfer( Node fact, Node exp, const char * c );
  void sendLemma( Node fact, Node reason, const char * c );
  void sendSplit( Node a, Node b, const char * c );
  void doPendingFacts();
  void doPendingSplitFacts();
  void addSharedTerm( TNode n );

  // Helper functions
  inline Node selectElement( Node, int);
  bool safeAddToMap( std::map< Node, std::vector<Node> >&, Node, Node );
  void addToMap( std::map< Node, std::vector<Node> >&, Node, Node );
  bool hasTuple( Node, Node );
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool exists( std::vector<Node>&, Node );
  bool holds( Node );
  void computeTupleReps( Node );
  void makeSharedTerm( Node );

};


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
