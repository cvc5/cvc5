/*********************                                                        */
/*! \file theory_sets_rels.cpp
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

#include "theory/sets/theory_sets_rels.h"

#include "expr/datatype.h"
//#include "options/sets_options.h"
//#include "smt/smt_statistics_registry.h"
//#include "theory/sets/expr_patterns.h" // ONLY included here
//#include "theory/sets/scrutinize.h"
//#include "theory/sets/theory_sets.h"
//#include "theory/theory_model.h"
//#include "util/result.h"


using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

  TheorySetsRels::TheorySetsRels(context::Context* c,
                                 context::UserContext* u,
                                 eq::EqualityEngine* eq,
                                 context::CDO<bool>* conflict):
    d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
    d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
    d_eqEngine(eq),
    d_conflict(conflict),
    d_relsSaver(c)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TRANSCLOSURE);
  }

  TheorySetsRels::~TheorySetsRels() {}

  void TheorySetsRels::check(Theory::Effort level) {

    Debug("rels-eqc") <<  "\nStart iterating equivalence classes......\n" << std::endl;

    if (!d_eqEngine->consistent())
      return;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );

    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_eqEngine );

      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);

        // only consider membership constraints that involving relatioinal operators
        if((d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_trueNode)
              || d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_falseNode))
            && !d_relsSaver.contains(n)) {

          // case: [NOT] (b, a) IS_IN (TRANSPOSE X)
          //    => [NOT] (a, b) IS_IN X
          if(n.getKind() == kind::MEMBER) {
            d_relsSaver.insert(n);
            if(kind::TRANSPOSE == n[1].getKind()) {
              Node reversedTuple = reverseTuple(n[0]);
              Node fact = NodeManager::currentNM()->mkNode(kind::MEMBER, reversedTuple, n[1][0]);
              Node exp = n;
              if(d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_falseNode)) {
                fact = fact.negate();
                exp = n.negate();
              }
              d_pending_facts[fact] = exp;
            } else if(kind::JOIN == n[1].getKind()) {
              TNode r1 = n[1][0];
              TNode r2 = n[1][1];
              // Need to do this efficiently... Join relations after collecting all of them
              // So that we would just need to iterate over EE once
              joinRelations(r1, r2, n[1].getType().getSetElementType());

              // case: (a, b) IS_IN (X JOIN Y)
              //      => (a, z) IS_IN X  && (z, b) IS_IN Y
              if(d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_trueNode)) {
                Debug("rels-join") << "Join rules (a, b) IS_IN (X JOIN Y) => ((a, z) IS_IN X  && (z, b) IS_IN Y)"<< std::endl;
                Assert((r1.getType().getSetElementType()).isDatatype());
                Assert((r2.getType().getSetElementType()).isDatatype());

                unsigned int i = 0;
                std::vector<Node> r1_tuple;
                std::vector<Node> r2_tuple;
                Node::iterator child_it = n[0].begin();
                unsigned int s1_len = r1.getType().getSetElementType().getTupleLength();
                Node shared_x = NodeManager::currentNM()->mkSkolem("sde_", r2.getType().getSetElementType().getTupleTypes()[0]);
                Datatype dt = r1.getType().getSetElementType().getDatatype();

                r1_tuple.push_back(Node::fromExpr(dt[0].getConstructor()));
                for(; i < s1_len-1; ++child_it) {
                  r1_tuple.push_back(*child_it);
                  ++i;
                }
                r1_tuple.push_back(shared_x);
                dt = r2.getType().getSetElementType().getDatatype();
                r2_tuple.push_back(Node::fromExpr(dt[0].getConstructor()));
                r2_tuple.push_back(shared_x);
                for(; child_it != n[0].end(); ++child_it) {
                  r2_tuple.push_back(*child_it);
                }
                Node t1 = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r1_tuple);
                Node t2 = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r2_tuple);
                Node f1 = NodeManager::currentNM()->mkNode(kind::MEMBER, t1, r1);
                Node f2 = NodeManager::currentNM()->mkNode(kind::MEMBER, t2, r2);
                d_pending_facts[f1] = n;
                d_pending_facts[f2] = n;
              }
            }else if(kind::PRODUCT == n[1].getKind()) {

            }
          }
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    doPendingFacts();
  }

  // Join all explicitly specified tuples in r1, r2
  // e.g. If (a, b) in X and (b, c) in Y, (a, c) in (X JOIN Y)
  void TheorySetsRels::joinRelations(TNode r1, TNode r2, TypeNode tn) {
    if (!d_eqEngine->consistent())
          return;
    Debug("rels-join") << "start joining tuples in "
                       << r1 << " and " << r2 << std::endl;

    std::vector<Node> r1_elements;
    std::vector<Node> r2_elements;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );

    // collect all tuples that are in r1, r2
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_eqEngine );
      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);
        if(d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_trueNode)
            && n.getKind() == kind::MEMBER && n[0].getType().isTuple()) {
          if(n[1] == r1) {
            Debug("rels-join") << "r1 tuple: " << n[0] << std::endl;
            r1_elements.push_back(n[0]);
          } else if (n[1] == r2) {
            Debug("rels-join") << "r2 tuple: " << n[0] << std::endl;
            r2_elements.push_back(n[0]);
          }
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    if(r1_elements.size() == 0 || r2_elements.size() == 0)
      return;

    // Join r1 and r2
    joinTuples(r1, r2, r1_elements, r2_elements, tn);

  }

  void TheorySetsRels::joinTuples(TNode r1, TNode r2, std::vector<Node>& r1_elements, std::vector<Node>& r2_elements, TypeNode tn) {
    Datatype dt = tn.getDatatype();
    unsigned int t1_len = r1_elements.front().getType().getTupleLength();
    unsigned int t2_len = r2_elements.front().getType().getTupleLength();

    for(unsigned int i = 0; i < r1_elements.size(); i++) {
      for(unsigned int j = 0; j < r2_elements.size(); j++) {
        if(r1_elements[i][t1_len-1] == r2_elements[j][0]) {
          std::vector<Node> joinedTuple;
          joinedTuple.push_back(Node::fromExpr(dt[0].getConstructor()));
          for(unsigned int k = 0; k < t1_len - 1; ++k) {
            joinedTuple.push_back(r1_elements[i][k]);
          }
          for(unsigned int l = 1; l < t2_len; ++l) {
            joinedTuple.push_back(r2_elements[j][l]);
          }
          Node fact = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, joinedTuple);
          fact = NodeManager::currentNM()->mkNode(kind::MEMBER, fact, NodeManager::currentNM()->mkNode(kind::JOIN, r1, r2));
          Node reason = NodeManager::currentNM()->mkNode(kind::AND,
                                                         NodeManager::currentNM()->mkNode(kind::MEMBER, r1_elements[i], r1),
                                                         NodeManager::currentNM()->mkNode(kind::MEMBER, r2_elements[j], r2));
          Debug("rels-join") << "join tuples: " << r1_elements[i]
                             << " and " << r2_elements[j]
                             << "\nnew fact: " << fact
                             << "\nreason: " << reason<< std::endl;
          d_pending_facts[fact] = reason;
        }
      }
    }
  }


  void TheorySetsRels::sendLemma(TNode fact, TNode reason, bool polarity) {

  }

  void TheorySetsRels::doPendingFacts() {
    std::map<Node, Node>::iterator map_it = d_pending_facts.begin();
    while( !(*d_conflict) && map_it != d_pending_facts.end()) {

      Node fact = map_it->first;
      Node exp = d_pending_facts[ fact ];
      Debug("rels") << "sending out pending fact: " << fact
                    << "  reason: " << exp
                    << std::endl;
      if(fact.getKind() == kind::AND) {
        for(size_t j=0; j<fact.getNumChildren(); j++) {
          bool polarity = fact[j].getKind() != kind::NOT;
          TNode atom = polarity ? fact[j] : fact[j][0];
          assertMembership(atom, exp, polarity);
        }
      } else {
        bool polarity = fact.getKind() != kind::NOT;
        TNode atom = polarity ? fact : fact[0];
        assertMembership(atom, exp, polarity);
      }
      map_it++;
    }
    d_pending_facts.clear();
  }



  Node TheorySetsRels::reverseTuple(TNode tuple) {
    Assert(tuple.getType().isTuple());

    std::vector<Node> elements;
    std::vector<TypeNode> tuple_types = tuple.getType().getTupleTypes();
    std::reverse(tuple_types.begin(), tuple_types.end());
    TypeNode tn = NodeManager::currentNM()->mkTupleType(tuple_types);
    Datatype dt = tn.getDatatype();

    elements.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(Node::iterator child_it = tuple.end()-1;
              child_it != tuple.begin()-1; --child_it) {
      elements.push_back(*child_it);
    }
    return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, elements);
  }

  void TheorySetsRels::assertMembership(TNode fact, TNode reason, bool polarity) {
    Debug("rels") << "fact: " << fact
                  << "\npolarity : " << polarity
                  << "\nreason: " << reason << std::endl;
    d_eqEngine->assertPredicate(fact, polarity, reason);
  }
}
}
}














