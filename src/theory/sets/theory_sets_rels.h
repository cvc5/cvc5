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

class TheorySetsRels {

  typedef context::CDChunkList<Node> NodeList;

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

  std::map< Node, std::vector<Node> > d_membership_cache;
  std::map< Node, std::vector<Node> > d_membership_exp_cache;
  std::map< Node, std::map<kind::Kind_t, std::vector<Node> > > d_terms_cache;

  eq::EqualityEngine *d_eqEngine;
  context::CDO<bool> *d_conflict;

  void check();
  void collectRelationalInfo();
  void assertMembership( Node fact, Node reason, bool polarity );
  void composeProductRelations( Node );
  void composeJoinRelations( Node );
  void composeTuplesForRels( Node );
  void applyTransposeRule( Node, Node, Node );
  void applyJoinRule( Node, Node, Node );
  void applyProductRule( Node, Node, Node );
  void computeJoinOrProductRelations( Node );
  void computeTransposeRelations( Node );
  Node reverseTuple( Node );

  void sendInfer( Node fact, Node exp, const char * c );
  void sendLemma( Node fact, Node reason, const char * c );
  void sendSplit( Node a, Node b, const char * c );
  void doPendingFacts();
  void doPendingSplitFacts();
  void addSharedTerm( TNode n );

  // Helper functions
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool exists( std::vector<Node>&, Node );
  bool holds(Node);

};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
