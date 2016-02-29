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
#include "theory/sets/expr_patterns.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/sets/theory_sets.h"
//#include "options/sets_options.h"
//#include "smt/smt_statistics_registry.h"
//#include "theory/sets/expr_patterns.h" // ONLY included here
//#include "theory/sets/scrutinize.h"
//#include "theory/sets/theory_sets.h"
//#include "theory/theory_model.h"
//#include "util/result.h"


using namespace std;
using namespace CVC4::expr::pattern;

namespace CVC4 {
namespace theory {
namespace sets {

typedef std::map<Node, std::map<kind::Kind_t, std::vector<Node> > >::iterator term_it;
typedef std::map<Node, std::vector<Node> >::iterator mem_it;

  void TheorySetsRels::check(Theory::Effort level) {
    Trace("rels-debug") << "[sets-rels] Start the relational solver..." << std::endl;
    collectRelationalInfo();
    check();
    doPendingSplitFacts();
    doPendingLemmas();
    Assert(d_lemma_cache.empty());
    Assert(d_pending_facts.empty());
    Trace("rels-debug") << "[sets-rels] Done with the relational solver..." << std::endl;
  }

  void TheorySetsRels::check() {
    mem_it m_it = d_membership_cache.begin();
    while(m_it != d_membership_cache.end()) {
      std::vector<Node> tuples = m_it->second;
      Node rel_rep = m_it->first;
      // No relational terms found with rel_rep as its representative
      if(d_terms_cache.find(rel_rep) == d_terms_cache.end()) {
        m_it++;
        continue;
      }
      for(unsigned int i = 0; i < tuples.size(); i++) {
        Node tup_rep = tuples[i];
        Node exp = d_membership_exp_cache[rel_rep][i];
        std::map<kind::Kind_t, std::vector<Node> > kind_terms = d_terms_cache[rel_rep];

        if(kind_terms.find(kind::TRANSPOSE) != kind_terms.end()) {
          std::vector<Node> tp_terms = kind_terms.at(kind::TRANSPOSE);
          // exp is a membership term and tp_terms contains all
          // transposed terms that are equal to the right hand side of exp
          for(unsigned int j = 0; j < tp_terms.size(); j++) {
            applyTransposeRule(exp, rel_rep, tp_terms[j]);
          }
        }
        if(kind_terms.find(kind::JOIN) != kind_terms.end()) {
          std::vector<Node> conj;
          std::vector<Node> join_terms = kind_terms.at(kind::JOIN);
          // exp is a membership term and join_terms contains all
          // joined terms that are in the same equivalence class with the right hand side of exp
          for(unsigned int j = 0; j < join_terms.size(); j++) {
            applyJoinRule(exp, rel_rep, join_terms[j]);
          }
        }
        if(kind_terms.find(kind::PRODUCT) != kind_terms.end()) {
          std::vector<Node> product_terms = kind_terms.at(kind::PRODUCT);
          for(unsigned int j = 0; j < product_terms.size(); j++) {
            applyProductRule(exp, rel_rep, product_terms[j]);
          }
        }
      }
      m_it++;
    }
  }



  void TheorySetsRels::collectRelationalInfo() {
    Trace("rels-debug") << "[sets-rels] Start collecting relational terms..." << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );
    while( !eqcs_i.isFinished() ){
      Node r = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_eqEngine );
      Trace("rels-ee") << "[sets-rels] term representative: " << r << std::endl;
      while( !eqc_i.isFinished() ){
        Node n = (*eqc_i);
        Trace("rels-ee") << "  term : " << n << std::endl;
        if(getRepresentative(r) == getRepresentative(d_trueNode) ||
           getRepresentative(r) == getRepresentative(d_falseNode)) {
          // collect membership info
          if(n.getKind() == kind::MEMBER && n[0].getType().isTuple()) {
            Node tup_rep = getRepresentative(n[0]);
            Node rel_rep = getRepresentative(n[1]);
            // No rel_rep is found
            if(d_membership_cache.find(rel_rep) == d_membership_cache.end()) {
              std::vector<Node> tups;
              tups.push_back(tup_rep);
              d_membership_cache[rel_rep] = tups;
              Node exp = n;
              if(getRepresentative(r) == getRepresentative(d_falseNode))
                exp = n.negate();
              tups.clear();
              tups.push_back(exp);
              d_membership_exp_cache[rel_rep] = tups;
            } else if(std::find(d_membership_cache.at(rel_rep).begin(),
                                d_membership_cache.at(rel_rep).end(), tup_rep)
                      == d_membership_cache.at(rel_rep).end()) {
              d_membership_cache[rel_rep].push_back(tup_rep);
              Node exp = n;
              if(getRepresentative(r) == getRepresentative(d_falseNode))
                exp = n.negate();
              d_membership_exp_cache.at(rel_rep).push_back(exp);
            }
          }
        // collect term info
        } else if(r.getType().isSet() && r.getType().getSetElementType().isTuple()) {
          if(n.getKind() == kind::TRANSPOSE ||
             n.getKind() == kind::JOIN ||
             n.getKind() == kind::PRODUCT ||
             n.getKind() == kind::TRANSCLOSURE) {
            std::map<kind::Kind_t, std::vector<Node> > rel_terms;
            std::vector<Node> terms;
            // No r record is found
            if(d_terms_cache.find(r) == d_terms_cache.end()) {
              terms.push_back(n);
              rel_terms[n.getKind()] = terms;
              d_terms_cache[r] = rel_terms;
            } else {
              rel_terms = d_terms_cache[r];
              // No n's kind record is found
              if(rel_terms.find(n.getKind()) == rel_terms.end()) {
                terms.push_back(n);
                rel_terms[n.getKind()] = terms;
              } else {
                rel_terms.at(n.getKind()).push_back(n);
              }
            }
          }
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    Trace("rels-debug") << "[sets-rels] Done with collecting relational terms!" << std::endl;
  }

  void TheorySetsRels::doPendingFacts() {
    std::map<Node, Node>::iterator map_it = d_pending_facts.begin();
    while( !(*d_conflict) && map_it != d_pending_facts.end()) {

      Node fact = map_it->first;
      Node exp = d_pending_facts[ fact ];
      if(fact.getKind() == kind::AND) {
        for(size_t j=0; j<fact.getNumChildren(); j++) {
          bool polarity = fact[j].getKind() != kind::NOT;
          Node atom = polarity ? fact[j] : fact[j][0];
          assertMembership(atom, exp, polarity);
        }
      } else {
        bool polarity = fact.getKind() != kind::NOT;
        Node atom = polarity ? fact : fact[0];
        assertMembership(atom, exp, polarity);
      }
      map_it++;
    }
    d_pending_facts.clear();
    d_membership_cache.clear();
    d_membership_exp_cache.clear();
    d_terms_cache.clear();
  }

  void TheorySetsRels::doPendingSplitFacts() {
      std::map<Node, Node>::iterator map_it = d_pending_split_facts.begin();
      while( !(*d_conflict) && map_it != d_pending_split_facts.end()) {

        Node fact = map_it->first;
        Node exp = d_pending_split_facts[ fact ];
        if(fact.getKind() == kind::AND) {
          for(size_t j=0; j<fact.getNumChildren(); j++) {
            bool polarity = fact[j].getKind() != kind::NOT;
            Node atom = polarity ? fact[j] : fact[j][0];
            assertMembership(atom, exp, polarity);
          }
        } else {
          bool polarity = fact.getKind() != kind::NOT;
          Node atom = polarity ? fact : fact[0];
          assertMembership(atom, exp, polarity);
        }
        map_it++;
      }
      d_pending_split_facts.clear();
    }

  void TheorySetsRels::applyProductRule(Node exp, Node rel_rep, Node product_term) {
    Trace("rels-debug") << "\n[sets-rels] Apply PRODUCT rule on term: " << product_term
                        << " with explaination: " << exp << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    if(!polarity)
      computeJoinOrProductRelations(product_term);
  }

  void TheorySetsRels::applyJoinRule(Node exp, Node rel_rep, Node join_term) {
    Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN rule on term: " << join_term
                        << " with explaination: " << exp << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node r1 = join_term[0];
    Node r2 = join_term[1];

    // case: (a, b) IS_IN (X JOIN Y)
    //      => (a, z) IS_IN X  && (z, b) IS_IN Y
    if(polarity) {
      Debug("rels-join") << "[sets-rels] Join rules (a, b) IS_IN (X JOIN Y) => "
                            "((a, z) IS_IN X  && (z, b) IS_IN Y)"<< std::endl;
      Assert((r1.getType().getSetElementType()).isDatatype());
      Assert((r2.getType().getSetElementType()).isDatatype());

      unsigned int i = 0;
      std::vector<Node> r1_tuple;
      std::vector<Node> r2_tuple;
      Node::iterator child_it = atom[0].begin();
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
      for(; child_it != atom[0].end(); ++child_it) {
        r2_tuple.push_back(*child_it);
      }
      Node t1 = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r1_tuple);
      Node t2 = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r2_tuple);
      Node f1 = NodeManager::currentNM()->mkNode(kind::MEMBER, t1, r1);
      Node f2 = NodeManager::currentNM()->mkNode(kind::MEMBER, t2, r2);
      Node reason = exp;
      if(atom[1] != join_term)
        reason = AND(reason, EQUAL(atom[1], join_term));
      sendInfer(f1, reason, "join-split");
      sendInfer(f2, reason, "join-split");
    } else {
      // ONLY need to explicitly compute joins if there are negative literals involving JOIN
      computeJoinOrProductRelations(join_term);
    }
  }

  void TheorySetsRels::applyTransposeRule(Node exp, Node rel_rep, Node tp_term) {
    Trace("rels-debug") << "\n[sets-rels] Apply transpose rule on term: " << tp_term
                        << " with explaination: " << exp << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node reversedTuple = reverseTuple(atom[0]);
    Node reason = exp;

    if(atom[1] != tp_term)
      reason = AND(reason, EQUAL(rel_rep, tp_term));
    Node fact = MEMBER(reversedTuple, tp_term[0]);

    // when the term is nested like (not tup is_in tp(x join/product y)),
    // we need to compute what is inside x join/product y
    if(!polarity) {
      if(d_terms_cache[getRepresentative(fact[1])].find(kind::JOIN)
         != d_terms_cache[getRepresentative(fact[1])].end()) {
        std::vector<Node> join_terms = d_terms_cache[getRepresentative(fact[1])][kind::JOIN];
        for(unsigned int i = 0; i < join_terms.size(); i++) {
          computeJoinOrProductRelations(join_terms[i]);
        }
      }
      if(d_terms_cache[getRepresentative(fact[1])].find(kind::PRODUCT)
         != d_terms_cache[getRepresentative(fact[1])].end()) {
        std::vector<Node> product_terms = d_terms_cache[getRepresentative(fact[1])][kind::PRODUCT];
        for(unsigned int i = 0; i < product_terms.size(); i++) {
          computeJoinOrProductRelations(product_terms[i]);
        }
      }
      fact = fact.negate();
    }
    sendInfer(fact, exp, "transpose-rule");
  }

  void TheorySetsRels::computeJoinOrProductRelations(Node n) {
    Trace("rels-debug") << "\n[sets-rels] computeJoinOrProductRelations for relation  " << n << std::endl;
    switch(n[0].getKind()) {
    case kind::TRANSPOSE:
      computeTransposeRelations(n[0]);
      break;
    case kind::JOIN:
    case kind::PRODUCT:
      computeJoinOrProductRelations(n[0]);
      break;
    default:
      break;
    }

    switch(n[1].getKind()) {
    case kind::TRANSPOSE:
      computeTransposeRelations(n[1]);
      break;
    case kind::JOIN:
    case kind::PRODUCT:
      computeJoinOrProductRelations(n[1]);
      break;
    default:
      break;
    }

    if(d_membership_cache.find(getRepresentative(n[0])) == d_membership_cache.end() ||
       d_membership_cache.find(getRepresentative(n[1])) == d_membership_cache.end())
          return;
    composeRelations(n);
  }

  void TheorySetsRels::computeTransposeRelations(Node n) {
    switch(n[0].getKind()) {
    case kind::JOIN:
      computeJoinOrProductRelations(n[0]);
      break;
    case kind::TRANSPOSE:
      computeTransposeRelations(n[0]);
      break;
    case kind::PRODUCT:
      computeJoinOrProductRelations(n[0]);
      break;
    default:
      break;
    }

    if(d_membership_cache.find(getRepresentative(n[0])) == d_membership_cache.end())
      return;
    std::vector<Node> rev_tuples;
    std::vector<Node> rev_exps;
    Node n_rep = getRepresentative(n);
    Node n0_rep = getRepresentative(n[0]);

    if(d_membership_cache.find(n_rep) != d_membership_cache.end()) {
      rev_tuples = d_membership_cache[n_rep];
      rev_exps = d_membership_exp_cache[n_rep];
    }
    std::vector<Node> tuples = d_membership_cache[n0_rep];
    std::vector<Node> exps = d_membership_exp_cache[n0_rep];
    for(unsigned int i = 0; i < tuples.size(); i++) {
      // Todo: Need to consider duplicates
      Node reason = exps[i];
      Node rev_tup = reverseTuple(tuples[i]);
      if(exps[i][1] != n0_rep)
        reason = AND(reason, EQUAL(exps[i][1], n0_rep));
      rev_tuples.push_back(rev_tup);
      rev_exps.push_back(Rewriter::rewrite(reason));
      sendInfer(MEMBER(rev_tup, n_rep), Rewriter::rewrite(reason), "transpose-rule");
    }
    d_membership_cache[n_rep] = rev_tuples;
    d_membership_exp_cache[n_rep] = rev_exps;
  }

  // Join all explicitly specified tuples in r1, r2
  // e.g. If (a, b) in X and (b, c) in Y, (a, c) in (X JOIN Y)
  void TheorySetsRels::composeRelations(Node n) {
    Node r1 = n[0];
    Node r2 = n[1];
    Node r1_rep = getRepresentative(r1);
    Node r2_rep = getRepresentative(r2);
    Trace("rels-debug") << "[sets-rels] start composing tuples in relations "
                       << r1 << " and " << r2
                       << "\n r1_rep: " << r1_rep
                       << "\n r2_rep: " << r2_rep << std::endl;

    if(d_membership_cache.find(r1_rep) == d_membership_cache.end() ||
       d_membership_cache.find(r2_rep) == d_membership_cache.end())
    return;

    TypeNode tn = n.getType().getSetElementType();
    Datatype dt = tn.getDatatype();
    std::vector<Node> new_tups;
    std::vector<Node> new_exps;
    std::vector<Node> r1_elements = d_membership_cache[r1_rep];
    std::vector<Node> r2_elements = d_membership_cache[r2_rep];
    std::vector<Node> r1_exps = d_membership_exp_cache[r1_rep];
    std::vector<Node> r2_exps = d_membership_exp_cache[r2_rep];
    Node new_rel = n.getKind() == kind::JOIN ? NodeManager::currentNM()->mkNode(kind::JOIN, r1_rep, r2_rep)
                                             : NodeManager::currentNM()->mkNode(kind::PRODUCT, r1_rep, r2_rep);
    unsigned int t1_len = r1_elements.front().getType().getTupleLength();
    unsigned int t2_len = r2_elements.front().getType().getTupleLength();

    for(unsigned int i = 0; i < r1_elements.size(); i++) {
      for(unsigned int j = 0; j < r2_elements.size(); j++) {
        std::vector<Node> joinedTuple;
        joinedTuple.push_back(Node::fromExpr(dt[0].getConstructor()));
        if((areEqual(r1_elements[i][t1_len-1], r2_elements[j][0]) && n.getKind() == kind::JOIN) ||
            n.getKind() == kind::PRODUCT) {
          unsigned int k = 0;
          unsigned int l = 1;
          for(; k < t1_len - 1; ++k) {
            joinedTuple.push_back(r1_elements[i][k]);
          }
          if(kind::PRODUCT == n.getKind()) {
            joinedTuple.push_back(r1_elements[i][k]);
            joinedTuple.push_back(r1_elements[j][0]);
          }
          for(; l < t2_len; ++l) {
            joinedTuple.push_back(r2_elements[j][l]);
          }
          Node fact = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, joinedTuple);
          new_tups.push_back(fact);
          fact = MEMBER(fact, new_rel);
          std::vector<Node> reasons;
          reasons.push_back(r1_exps[i]);
          reasons.push_back(r2_exps[j]);

          //Todo: think about how to deal with shared terms(?)
          if(n.getKind() == kind::JOIN)
            reasons.push_back(EQUAL(r1_elements[i][t1_len-1], r2_elements[j][0]));

          if(r1 != r1_rep) {
            reasons.push_back(EQUAL(r1, r1_rep));
          }
          if(r2 != r2_rep) {
            reasons.push_back(EQUAL(r2, r2_rep));
          }
          Node reason = theory::Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, reasons));
          new_exps.push_back(reason);
          Trace("rels-debug") << "[sets-rels] compose tuples: " << r1_elements[i]
                             << " and " << r2_elements[j]
                             << "\n new fact: " << fact
                             << "\n reason: " << reason<< std::endl;
          if(kind::JOIN == n.getKind())
            sendInfer(fact, reason, "join-compose");
          else if(kind::PRODUCT == n.getKind())
            sendInfer( fact, reason, "product-compose" );
        }
      }
    }

    Node new_rel_rep = getRepresentative( new_rel );
    if(d_membership_cache.find( new_rel_rep ) != d_membership_cache.end()) {
      std::vector<Node> tups = d_membership_cache[new_rel_rep];
      std::vector<Node> exps = d_membership_exp_cache[new_rel_rep];
      // Todo: Need to take care of duplicate tuples
      tups.insert( tups.end(), new_tups.begin(), new_tups.end() );
      exps.insert( exps.end(), new_exps.begin(), new_exps.end() );
    } else {
      d_membership_cache[new_rel_rep] = new_tups;
      d_membership_exp_cache[new_rel_rep] = new_exps;
    }
    Trace("rels-debug") << "[sets-rels] Done with joining tuples !" << std::endl;
  }

  void TheorySetsRels::doPendingLemmas() {
    if( !(*d_conflict) && (!d_lemma_cache.empty() || !d_pending_facts.empty())){
      for( unsigned i=0; i < d_lemma_cache.size(); i++ ){
        Trace("rels-debug") << "[sets-rels] Process pending lemma : " << d_lemma_cache[i] << std::endl;
        d_sets.d_out->lemma( d_lemma_cache[i] );
      }
      for( std::map<Node, Node>::iterator child_it = d_pending_facts.begin();
           child_it != d_pending_facts.end(); child_it++ ) {
        if(holds(child_it->first)) {
          Trace("rels-debug") << "[sets-rels] Skip the already processed fact,: " << child_it->first << std::endl;
          continue;
        }

        Trace("rels-debug") << "[sets-rels] Process pending fact as lemma : " << child_it->first << std::endl;
        d_sets.d_out->lemma(child_it->first);
      }
    }
    d_pending_facts.clear();
    d_lemma_cache.clear();
  }

  void TheorySetsRels::sendSplit(Node a, Node b, const char * c) {
    Node eq = a.eqNode( b );
    Node neq = NOT( eq );
    Node lemma_or = OR( eq, neq );
    Trace("rels-lemma") << "[sets-rels] Lemma " << c << " SPLIT : " << lemma_or << std::endl;
    d_lemma_cache.push_back( lemma_or );
  }

  void TheorySetsRels::sendLemma(Node fact, Node reason, bool polarity) {

  }

  void TheorySetsRels::sendInfer( Node fact, Node exp, const char * c ) {
    Trace("rels-lemma") << "[sets-rels] Infer " << fact << " from " << exp << " by " << c << std::endl;
    if( std::strcmp( c, "join-split" ) == 0 ) {
      d_pending_split_facts[fact] = exp;
      return;
    }
    d_pending_facts[fact] = exp;
    d_infer.push_back( fact );
    d_infer_exp.push_back( exp );
  }

  Node TheorySetsRels::reverseTuple( Node tuple ) {
    Assert( tuple.getType().isTuple() );
    std::vector<Node> elements;
    std::vector<TypeNode> tuple_types = tuple.getType().getTupleTypes();
    std::reverse( tuple_types.begin(), tuple_types.end() );
    TypeNode tn = NodeManager::currentNM()->mkTupleType( tuple_types );
    Datatype dt = tn.getDatatype();

    elements.push_back( Node::fromExpr(dt[0].getConstructor() ) );
    for(Node::iterator child_it = tuple.end()-1;
        child_it != tuple.begin()-1; --child_it) {
      elements.push_back( *child_it );
    }
    return NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, elements );
  }

  void TheorySetsRels::assertMembership( Node fact, Node reason, bool polarity ) {
    d_eqEngine->assertPredicate( fact, polarity, reason );
  }

  Node TheorySetsRels::getRepresentative( Node t ) {
    if( d_eqEngine->hasTerm( t ) ){
      return d_eqEngine->getRepresentative( t );
    }else{
      return t;
    }
  }

  bool TheorySetsRels::hasTerm( Node a ){
    return d_eqEngine->hasTerm( a );
  }

  bool TheorySetsRels::areEqual( Node a, Node b ){
    if( hasTerm( a ) && hasTerm( b ) ){
      if( d_eqEngine->isTriggerTerm(a, THEORY_SETS) &&
          d_eqEngine->isTriggerTerm(b, THEORY_SETS) ) {
        // Get representative trigger terms
          TNode x_shared = d_eqEngine->getTriggerTermRepresentative(a, THEORY_SETS);
          TNode y_shared = d_eqEngine->getTriggerTermRepresentative(b, THEORY_SETS);
          EqualityStatus eqStatusDomain = d_sets.d_valuation.getEqualityStatus(x_shared, y_shared);
          switch (eqStatusDomain) {
            case EQUALITY_TRUE_AND_PROPAGATED:
              // Should have been propagated to us
              Trace("rels-debug") << "EQUALITY_TRUE_AND_PROPAGATED ****  equality( a, b ) = true" << std::endl;
              return true;
              break;
            case EQUALITY_TRUE:
              // Missed propagation - need to add the pair so that theory engine can force propagation
              Trace("rels-debug") << "EQUALITY_TRUE **** equality( a, b ) = true" << std::endl;
              return true;
              break;
            case EQUALITY_FALSE_AND_PROPAGATED:
              // Should have been propagated to us
              Trace("rels-debug") << "EQUALITY_FALSE_AND_PROPAGATED ******** equality( a, b ) = false" << std::endl;
              return false;
              break;
            case EQUALITY_FALSE:
              Trace("rels-debug") << "EQUALITY_FALSE **** equality( a, b ) = false" << std::endl;
              return false;
              break;

            default:
              // Covers EQUALITY_TRUE_IN_MODEL (common case) and EQUALITY_UNKNOWN
              break;
          }
      }
      Trace("rels-debug") << "has a and b " << a << " " << b << " are equal? "<<  d_eqEngine->areEqual( a, b ) << std::endl;
      return d_eqEngine->areEqual( a, b );
    }else if( a.isConst() && b.isConst() ){
      return a == b;
    }else {
      Trace("rels-debug") << "to split a and b " << a << " " << b << std::endl;
      addSharedTerm(a);
      addSharedTerm(b);
      sendSplit(a, b, "tuple-element-equality");
      return false;
    }
  }

  void TheorySetsRels::addSharedTerm(TNode n) {
    Trace("rels-debug") << "[sets-rels] Add a shared term:  " << n << std::endl;
    d_sets.addSharedTerm(n);
    d_eqEngine->addTriggerTerm(n, THEORY_SETS);
  }

  bool TheorySetsRels::exists( std::vector<Node>& v, Node n ){
    return std::find(v.begin(), v.end(), n) != v.end();
  }

  bool TheorySetsRels::holds(Node node) {
    bool polarity = node.getKind() != kind::NOT;
    Node atom = polarity ? node : node[0];
    Node polarity_atom = polarity ? d_trueNode : d_falseNode;
    Node atom_mod = NodeManager::currentNM()->mkNode(atom.getKind(), getRepresentative(atom[0]),
                                                      getRepresentative(atom[1]) );
    d_eqEngine->addTerm(atom_mod);
    return areEqual(atom_mod, polarity_atom);
  }

  TheorySetsRels::TheorySetsRels(context::Context* c,
                                 context::UserContext* u,
                                 eq::EqualityEngine* eq,
                                 context::CDO<bool>* conflict,
                                 TheorySets& d_set):
    d_sets(d_set),
    d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
    d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
    d_infer(c),
    d_infer_exp(c),
    d_eqEngine(eq),
    d_conflict(conflict)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TRANSCLOSURE);
  }

  TheorySetsRels::~TheorySetsRels() {}


}
}
}














