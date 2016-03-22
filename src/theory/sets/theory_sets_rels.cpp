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
    Trace("rels") << "\n[sets-rels] ******************************* Start the relational solver *******************************\n" << std::endl;
    collectRelsInfo();
    check();
    doPendingLemmas();
    Assert(d_lemma_cache.empty());
    Assert(d_pending_facts.empty());
    Trace("rels") << "\n[sets-rels] ******************************* Done with the relational solver *******************************\n" << std::endl;
  }

  void TheorySetsRels::check() {
    mem_it m_it = d_membership_cache.begin();
    while(m_it != d_membership_cache.end()) {
      Node rel_rep = m_it->first;

      // No relational terms found with rel_rep as its representative
      if(d_terms_cache.find(rel_rep) == d_terms_cache.end()) {
        // TRANSPOSE(rel_rep) may occur in the context
        Node tp_rel = NodeManager::currentNM()->mkNode(kind::TRANSPOSE, rel_rep);
        Node tp_rel_rep = getRepresentative(tp_rel);
        if(d_terms_cache.find(tp_rel_rep) != d_terms_cache.end()) {
          for(unsigned int i = 0; i < m_it->second.size(); i++) {
            Node exp = tp_rel == tp_rel_rep ? d_membership_exp_cache[rel_rep][i]
                                            : AND(d_membership_exp_cache[rel_rep][i], EQUAL(tp_rel, tp_rel_rep));
            // Lazily apply transpose-occur rule.
            // Need to eagerly apply if we don't send facts as lemmas
            applyTransposeRule(exp, tp_rel_rep, true);
          }
        }
      } else {
        for(unsigned int i = 0; i < m_it->second.size(); i++) {
          Node exp = d_membership_exp_cache[rel_rep][i];
          std::map<kind::Kind_t, std::vector<Node> > kind_terms = d_terms_cache[rel_rep];

          if(kind_terms.find(kind::TRANSPOSE) != kind_terms.end()) {
            std::vector<Node> tp_terms = kind_terms[kind::TRANSPOSE];
            // exp is a membership term and tp_terms contains all
            // transposed terms that are equal to the right hand side of exp
            for(unsigned int j = 0; j < tp_terms.size(); j++) {
              applyTransposeRule(exp, tp_terms[j]);
            }
          }
          if(kind_terms.find(kind::JOIN) != kind_terms.end()) {
            std::vector<Node> join_terms = kind_terms[kind::JOIN];
            Trace("rels-debug") << "[sets-rels] apply join rules on join terms with size = " << join_terms.size() << std::endl;
            // exp is a membership term and join_terms contains all
            // terms involving "join" operator that are in the same equivalence class with the right hand side of exp
            for(unsigned int j = 0; j < join_terms.size(); j++) {
              Trace("rels-debug") << "[sets-rels] join term = " << join_terms[j] << std::endl;
              applyJoinRule(exp, join_terms[j]);
            }
          }
          if(kind_terms.find(kind::PRODUCT) != kind_terms.end()) {
            std::vector<Node> product_terms = kind_terms[kind::PRODUCT];
            for(unsigned int j = 0; j < product_terms.size(); j++) {
              applyProductRule(exp, product_terms[j]);
            }
          }
        }
      }
      m_it++;
    }
  }

  /*
   * Polulate the relational terms data structure
   */

  void TheorySetsRels::collectRelsInfo() {
    Trace("rels-debug") << "[sets-rels] Start collecting relational terms..." << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );
    while( !eqcs_i.isFinished() ){
      Node r = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_eqEngine );
      Trace("rels-ee") << "[sets-rels-ee] term representative: " << r << std::endl;
      while( !eqc_i.isFinished() ){
        Node n = (*eqc_i);
        Trace("rels-ee") << "  term : " << n << std::endl;
        if(getRepresentative(r) == getRepresentative(d_trueNode) ||
           getRepresentative(r) == getRepresentative(d_falseNode)) {
          // collect membership info
          if(n.getKind() == kind::MEMBER && n[1].getType().getSetElementType().isTuple()) {
            Node tup_rep = getRepresentative(n[0]);
            Node rel_rep = getRepresentative(n[1]);
            // Todo: check n[0] or n[0]'s rep is a var??
            if(n[0].isVar()){
              reduceTupleVar(n);
            } else {
              if(safeAddToMap(d_membership_cache, rel_rep, tup_rep)) {
                bool true_eq = areEqual(r, d_trueNode);
                Node reason = true_eq ? n : n.negate();
                addToMap(d_membership_exp_cache, rel_rep, reason);
                if(true_eq) {
                  addToMembershipDB(rel_rep, tup_rep, reason);
                }
              }
            }
          }
        // collect relational terms info
        } else if( r.getType().isSet() && r.getType().getSetElementType().isTuple() ) {
          if( n.getKind() == kind::TRANSPOSE ||
              n.getKind() == kind::JOIN ||
              n.getKind() == kind::PRODUCT ||
              n.getKind() == kind::TRANSCLOSURE ) {
            std::map<kind::Kind_t, std::vector<Node> > rel_terms;
            std::vector<Node> terms;
            // No r record is found
            if( d_terms_cache.find(r) == d_terms_cache.end() ) {
              terms.push_back(n);
              rel_terms[n.getKind()] = terms;
              d_terms_cache[r] = rel_terms;
            } else {
              // No n's kind record is found
              if( d_terms_cache[r].find(n.getKind()) == d_terms_cache[r].end() ) {
                terms.push_back(n);
                d_terms_cache[r][n.getKind()] = terms;
              } else {
                d_terms_cache[r][n.getKind()].push_back(n);
              }
            }
          }
        // need to add all tuple elements as shared terms
        } else if(n.getType().isTuple() && !n.isConst() && !n.isVar()) {
          for(unsigned int i = 0; i < n.getType().getTupleLength(); i++) {
            Node element = selectElement(n, i);
            if(!element.isConst()) {
              makeSharedTerm(element);
            }
          }
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    Trace("rels-debug") << "[sets-rels] Done with collecting relational terms!" << std::endl;
  }

 /*  product-split rule:    (a, b) IS_IN (X PRODUCT Y)
  *                  ----------------------------------
  *                       a IS_IN X  && b IS_IN Y
  *
  *  product-compose rule: (a, b) IS_IN X    (c, d) IS_IN Y  NOT (r, s, t, u) IS_IN (X PRODUCT Y)
  *                        ----------------------------------------------------------------------
  *                                         (a, b, c, d) IS_IN (X PRODUCT Y)
  */

  void TheorySetsRels::applyProductRule(Node exp, Node product_term) {
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node r1_rep = getRepresentative(product_term[0]);
    Node r2_rep = getRepresentative(product_term[1]);

    if(polarity & d_lemma.find(exp) != d_lemma.end()) {
      Trace("rels-debug") << "\n[sets-rels] Apply PRODUCT-SPLIT rule on term: " << product_term
                          << " with explaination: " << exp << std::endl;
      std::vector<Node> r1_element;
      std::vector<Node> r2_element;

      NodeManager *nm = NodeManager::currentNM();
      Datatype dt = r1_rep.getType().getSetElementType().getDatatype();
      unsigned int i = 0;
      unsigned int s1_len = r1_rep.getType().getSetElementType().getTupleLength();
      unsigned int tup_len = product_term.getType().getSetElementType().getTupleLength();

      r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      for(; i < s1_len; ++i) {
        r1_element.push_back(selectElement(atom[0], i));
      }

      dt = r2_rep.getType().getSetElementType().getDatatype();
      r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      for(; i < tup_len; ++i) {
        r2_element.push_back(selectElement(atom[0], i));
      }

      Node fact;
      Node reason = exp;
      Node t1 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element));
      Node t2 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element));

      if(!hasTuple(r1_rep, t1)) {
        fact = MEMBER( t1, r1_rep );
        if(r1_rep != product_term[0])
          reason = Rewriter::rewrite(AND(reason, EQUAL(r1_rep, product_term[0])));
        addToMap(d_membership_db, r1_rep, t1);
        addToMap(d_membership_exp_db, r1_rep, reason);
        sendInfer(fact, reason, "product-split");
      }

      if(!hasTuple(r2_rep, t2)) {
        fact = MEMBER( t2, r2_rep );
        if(r2_rep != product_term[1])
          reason = Rewriter::rewrite(AND(reason, EQUAL(r2_rep, product_term[1])));
        addToMap(d_membership_db, r2_rep, t2);
        addToMap(d_membership_exp_db, r2_rep, reason);
        sendInfer(fact, reason, "product-split");
      }
    } else {
      // ONLY need to explicitly compute joins if there are negative literals involving PRODUCT
      Trace("rels-debug") << "\n[sets-rels] Apply PRODUCT-COMPOSE rule on term: " << product_term
                          << " with explaination: " << exp << std::endl;
      computeRels(product_term);
    }
  }

  /* join-split rule:           (a, b) IS_IN (X JOIN Y)
   *                  --------------------------------------------
   *                  exists z | (a, z) IS_IN X  && (z, b) IS_IN Y
   *
   *
   * join-compose rule: (a, b) IS_IN X    (b, c) IS_IN Y  NOT (t, u) IS_IN (X JOIN Y)
   *                    -------------------------------------------------------------
   *                                      (a, c) IS_IN (X JOIN Y)
   */
  void TheorySetsRels::applyJoinRule(Node exp, Node join_term) {
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node r1_rep = getRepresentative(join_term[0]);
    Node r2_rep = getRepresentative(join_term[1]);

    if(polarity && d_lemma.find(exp) != d_lemma.end()) {
      Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN-SPLIT rule on term: " << join_term
                          << " with explaination: " << exp << std::endl;

      std::vector<Node> r1_element;
      std::vector<Node> r2_element;
      NodeManager *nm = NodeManager::currentNM();
      TypeNode shared_type = r2_rep.getType().getSetElementType().getTupleTypes()[0];
      Node shared_x = nm->mkSkolem("sde_", shared_type);
      Datatype dt = r1_rep.getType().getSetElementType().getDatatype();
      unsigned int i = 0;
      unsigned int s1_len = r1_rep.getType().getSetElementType().getTupleLength();
      unsigned int tup_len = join_term.getType().getSetElementType().getTupleLength();

      r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      for(; i < s1_len-1; ++i) {
        r1_element.push_back(selectElement(atom[0], i));
      }
      r1_element.push_back(shared_x);

      dt = r2_rep.getType().getSetElementType().getDatatype();
      r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      r2_element.push_back(shared_x);
      for(; i < tup_len; ++i) {
        r2_element.push_back(selectElement(atom[0], i));
      }

      Node t1 = nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element);
      Node t2 = nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element);
      computeTupleReps(t1);
      computeTupleReps(t2);
      std::vector<Node> elements = d_membership_trie[r1_rep].findTerms(d_tuple_reps[t1]);

      if(elements.size() != 0) {
        for(unsigned int j = 0; j < elements.size(); j++) {
          std::vector<Node> new_tup;
          new_tup.push_back(elements[j]);
          new_tup.insert(new_tup.end(), d_tuple_reps[t2].begin()+1, d_tuple_reps[t2].end());
          if(d_membership_trie[r2_rep].existsTerm(new_tup) != Node::null()) {
            return;
          }
        }
      }
      Node fact;
      Node reason = atom[1] == join_term ? exp : AND(exp, EQUAL(atom[1], join_term));
      Node reasons = reason;

      fact = MEMBER(t1, r1_rep);
      if(r1_rep != join_term[0])
        reasons = Rewriter::rewrite(AND(reason, EQUAL(r1_rep, join_term[0])));
      addToMembershipDB(r1_rep, t1, reasons);
      sendInfer(fact, reasons, "join-split");

      reasons = reason;
      fact = MEMBER(t2, r2_rep);
      if(r2_rep != join_term[1])
        reasons = Rewriter::rewrite(AND(reason, EQUAL(r2_rep, join_term[1])));
      addToMembershipDB(r2_rep, t2, reasons);
      sendInfer(fact, reasons, "join-split");

      // Need to make the skolem "shared_x" as shared term
      makeSharedTerm(shared_x);
    } else {
      // ONLY need to explicitly compute joins if there are negative literals involving JOIN
      Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN-COMPOSE rule on term: " << join_term
                          << " with explaination: " << exp << std::endl;
      computeRels(join_term);
    }
  }

  /*
   * transpose-occur rule:   [NOT] (a, b) IS_IN X   (TRANSPOSE X) occurs
   *                         -------------------------------------------------------
   *                                   [NOT] (b, a) IS_IN (TRANSPOSE X)
   *
   * transpose rule:       [NOT] (a, b) IS_IN (TRANSPOSE X)
   *                ------------------------------------------------
   *                            [NOT] (b, a) IS_IN X
   */
  void TheorySetsRels::applyTransposeRule(Node exp, Node tp_term, bool tp_occur) {
    Trace("rels-debug") << "\n[sets-rels] Apply transpose rule on term: " << tp_term
                        << " with explaination: " << exp << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node reversedTuple = getRepresentative(reverseTuple(atom[0]));

    if(tp_occur) {
      Node fact = polarity ? MEMBER(reversedTuple, tp_term) : MEMBER(reversedTuple, tp_term).negate();
      if(holds(fact)) {
        Trace("rels-debug") << "[sets-rels] New fact: " << fact << " already holds. Skip...." << std::endl;
      } else {
        sendInfer(fact, exp, "transpose-occur");
        if(polarity) {
          addToMembershipDB(tp_term, reversedTuple, exp);
        }
      }
      return;
    }

    Node tp_t0_rep = getRepresentative(tp_term[0]);
    Node reason = atom[1] == tp_term ? exp : Rewriter::rewrite(AND(exp, EQUAL(atom[1], tp_term)));
    Node fact = MEMBER(reversedTuple, tp_t0_rep);

    if(!polarity) {
      // tp_term is a nested term and we eagerly compute its subterms' members
      if(d_terms_cache[tp_t0_rep].find(kind::JOIN)
         != d_terms_cache[tp_t0_rep].end()) {
        std::vector<Node> join_terms = d_terms_cache[tp_t0_rep][kind::JOIN];
        for(unsigned int i = 0; i < join_terms.size(); i++) {
          computeRels(join_terms[i]);
        }
      }
      if(d_terms_cache[tp_t0_rep].find(kind::PRODUCT)
         != d_terms_cache[tp_t0_rep].end()) {
        std::vector<Node> product_terms = d_terms_cache[tp_t0_rep][kind::PRODUCT];
        for(unsigned int i = 0; i < product_terms.size(); i++) {
          computeRels(product_terms[i]);
        }
      }
      fact = fact.negate();
    }
    if(holds(fact)) {
      Trace("rels-debug") << "[sets-rels] New fact: " << fact << " already holds. Skip...." << std::endl;
    } else {
      sendInfer(fact, reason, "transpose-rule");
      if(polarity) {
        addToMembershipDB(tp_t0_rep, reversedTuple, reason);
      }
    }
  }

  // Bottom-up fashion to compute relations
  void TheorySetsRels::computeRels(Node n) {
    Trace("rels-debug") << "\n[sets-rels] computeJoinOrProductRelations for relation  " << n << std::endl;
    switch(n[0].getKind()) {
    case kind::TRANSPOSE:
      computeTransposeRelations(n[0]);
      break;
    case kind::JOIN:
    case kind::PRODUCT:
      computeRels(n[0]);
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
      computeRels(n[1]);
      break;
    default:
      break;
    }

    if(d_membership_db.find(getRepresentative(n[0])) == d_membership_db.end() ||
       d_membership_db.find(getRepresentative(n[1])) == d_membership_db.end())
          return;
    composeTuplesForRels(n);
  }

  void TheorySetsRels::computeTransposeRelations(Node n) {
    switch(n[0].getKind()) {
    case kind::TRANSPOSE:
      computeTransposeRelations(n[0]);
      break;
    case kind::JOIN:
    case kind::PRODUCT:
      computeRels(n[0]);
      break;
    default:
      break;
    }

    if(d_membership_db.find(getRepresentative(n[0])) == d_membership_db.end())
      return;

    Node n_rep = getRepresentative(n);
    Node n0_rep = getRepresentative(n[0]);
    std::vector<Node> tuples = d_membership_db[n0_rep];
    std::vector<Node> exps = d_membership_exp_db[n0_rep];
    Assert(tuples.size() == exps.size());
    for(unsigned int i = 0; i < tuples.size(); i++) {
      Node reason = exps[i][1] == n0_rep ? exps[i] : AND(exps[i], EQUAL(exps[i][1], n0_rep));
      Node rev_tup = getRepresentative(reverseTuple(tuples[i]));
      Node fact = MEMBER(rev_tup, n_rep);
      if(holds(fact)) {
        Trace("rels-debug") << "[sets-rels] New fact: " << fact << " already holds! Skip..." << std::endl;
      } else {
        addToMembershipDB(n_rep, rev_tup, Rewriter::rewrite(reason));
        sendInfer(fact, Rewriter::rewrite(reason), "transpose-rule");
      }
    }
  }

  /*
   * Explicitly compose the join or product relations of r1 and r2
   * e.g. If (a, b) in X and (b, c) in Y, (a, c) in (X JOIN Y)
   *
   */
  void TheorySetsRels::composeTuplesForRels( Node n ) {
    Node r1 = n[0];
    Node r2 = n[1];
    Node r1_rep = getRepresentative(r1);
    Node r2_rep = getRepresentative(r2);
    NodeManager* nm = NodeManager::currentNM();
    Trace("rels-debug") << "[sets-rels] start composing tuples in relations "
                        << r1 << " and " << r2 << std::endl;

    if(d_membership_db.find(r1_rep) == d_membership_db.end() ||
       d_membership_db.find(r2_rep) == d_membership_db.end())
    return;

    std::vector<Node> new_tups;
    std::vector<Node> new_exps;
    std::vector<Node> r1_elements = d_membership_db[r1_rep];
    std::vector<Node> r2_elements = d_membership_db[r2_rep];
    std::vector<Node> r1_exps = d_membership_exp_db[r1_rep];
    std::vector<Node> r2_exps = d_membership_exp_db[r2_rep];
    Node new_rel = n.getKind() == kind::JOIN ? nm->mkNode(kind::JOIN, r1_rep, r2_rep)
                                             : nm->mkNode(kind::PRODUCT, r1_rep, r2_rep);

    Node new_rel_rep = getRepresentative(new_rel);
    unsigned int t1_len = r1_elements.front().getType().getTupleLength();
    unsigned int t2_len = r2_elements.front().getType().getTupleLength();

    for(unsigned int i = 0; i < r1_elements.size(); i++) {
      for(unsigned int j = 0; j < r2_elements.size(); j++) {
        std::vector<Node> composed_tuple;
        TypeNode tn = n.getType().getSetElementType();
        Node r2_lmost = selectElement(r2_elements[j], 0);
        Node r1_rmost = selectElement(r1_elements[i], t1_len-1);
        composed_tuple.push_back(Node::fromExpr(tn.getDatatype()[0].getConstructor()));

        if((areEqual(r1_rmost, r2_lmost) && n.getKind() == kind::JOIN) ||
            n.getKind() == kind::PRODUCT) {
          bool isProduct = n.getKind() == kind::PRODUCT;
          unsigned int k = 0;
          unsigned int l = 1;
          for(; k < t1_len - 1; ++k) {
            composed_tuple.push_back(selectElement(r1_elements[i], k));
          }
          if(isProduct) {
            composed_tuple.push_back(selectElement(r1_elements[i], k));
            composed_tuple.push_back(selectElement(r2_elements[j], 0));
          }
          for(; l < t2_len; ++l) {
            composed_tuple.push_back(selectElement(r2_elements[j], l));
          }
          Node composed_tuple_rep = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, composed_tuple));
          Node fact = MEMBER(composed_tuple_rep, new_rel_rep);
          if(holds(fact)) {
            Trace("rels-debug") << "[sets-rels] New fact: " << fact << " already holds! Skip..." << std::endl;
          } else {
            std::vector<Node> reasons;
            reasons.push_back(r1_exps[i]);
            reasons.push_back(r2_exps[j]);
            if(!isProduct)
              reasons.push_back(EQUAL(r1_rmost, r2_lmost));
            if(r1 != r1_rep) {
              reasons.push_back(EQUAL(r1, r1_rep));
            }
            if(r2 != r2_rep) {
              reasons.push_back(EQUAL(r2, r2_rep));
            }

            Node reason = Rewriter::rewrite(nm->mkNode(kind::AND, reasons));
            addToMembershipDB(new_rel_rep, composed_tuple_rep, reason);

            if(isProduct)
              sendInfer( fact, reason, "product-compose" );
            else
              sendInfer( fact, reason, "join-compose" );

            Trace("rels-debug") << "[sets-rels] Compose tuples: " << r1_elements[i]
                               << " and " << r2_elements[j]
                               << "\n            Produce a new fact: " << fact
                               << "\n            Reason: " << reason<< std::endl;
          }
        }
      }
    }
    Trace("rels-debug") << "[sets-rels] Done with composing tuples !" << std::endl;
  }

  void TheorySetsRels::doPendingLemmas() {
    if( !(*d_conflict) && (!d_lemma_cache.empty() || !d_pending_facts.empty())){
      for( unsigned i=0; i < d_lemma_cache.size(); i++ ){
        if(holds( d_lemma_cache[i] )) {
          Trace("rels-lemma") << "[sets-rels-lemma-skip] Skip the already held lemma: "
                              << d_lemma_cache[i]<< std::endl;
          continue;
        }
        Trace("rels-lemma") << "[sets-rels-lemma] Process pending lemma : "
                            << d_lemma_cache[i] << std::endl;
        d_sets.d_out->lemma( d_lemma_cache[i] );
      }
      for( std::map<Node, Node>::iterator child_it = d_pending_facts.begin();
           child_it != d_pending_facts.end(); child_it++ ) {
        if(holds(child_it->first)) {
          Trace("rels-lemma") << "[sets-rels-fact-lemma-skip] Skip the already held fact,: "
                              << child_it->first << std::endl;
          continue;
        }
        Trace("rels-lemma") << "[sets-rels-fact-lemma] Process pending fact as lemma : "
                            << child_it->first << " with reason " << child_it->second << std::endl;
        d_sets.d_out->lemma(NodeManager::currentNM()->mkNode(kind::IMPLIES, child_it->second, child_it->first));
      }
    }
    d_pending_facts.clear();
    d_membership_cache.clear();
    d_membership_exp_cache.clear();
    d_membership_db.clear();
    d_membership_exp_db.clear();
    d_terms_cache.clear();
    d_lemma_cache.clear();
    d_membership_trie.clear();
    d_tuple_reps.clear();
  }

  void TheorySetsRels::sendSplit(Node a, Node b, const char * c) {
    Node eq = a.eqNode( b );
    Node neq = NOT( eq );
    Node lemma_or = OR( eq, neq );
    Trace("rels-lemma") << "[sets-lemma] Lemma " << c << " SPLIT : " << lemma_or << std::endl;
    d_lemma_cache.push_back( lemma_or );
  }

  void TheorySetsRels::sendLemma(Node conc, Node ant, const char * c) {
    Trace("rels-lemma") << "[sets-lemma] Infer " << conc << " from " << ant << " by " << c << std::endl;
    Node lemma = NodeManager::currentNM()->mkNode(kind::IMPLIES, ant, conc);
    d_lemma_cache.push_back(lemma);
    d_lemma.insert(lemma);
  }

  void TheorySetsRels::sendInfer( Node fact, Node exp, const char * c ) {
    Trace("rels-lemma") << "[sets-fact] Infer " << fact << " from " << exp << " by " << c << std::endl;
    d_pending_facts[fact] = exp;
    d_infer.push_back( fact );
    d_infer_exp.push_back( exp );
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
    d_membership_db.clear();
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
        Trace("rels-lemma") << "[sets-split-fact] Send " << fact << " from " << exp << std::endl;
        bool polarity = fact.getKind() != kind::NOT;
        Node atom = polarity ? fact : fact[0];
        assertMembership(atom, exp, polarity);
      }
      map_it++;
    }
    d_pending_split_facts.clear();
  }

  Node TheorySetsRels::reverseTuple( Node tuple ) {
    Assert( tuple.getType().isTuple() );
    std::vector<Node> elements;
    std::vector<TypeNode> tuple_types = tuple.getType().getTupleTypes();
    std::reverse( tuple_types.begin(), tuple_types.end() );
    TypeNode tn = NodeManager::currentNM()->mkTupleType( tuple_types );
    Datatype dt = tn.getDatatype();
    elements.push_back( Node::fromExpr(dt[0].getConstructor() ) );
    for(int i = tuple_types.size() - 1; i >= 0; --i) {
      elements.push_back( selectElement(tuple, i) );
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
    if(a == b) {
      return true;
    } else if(a.isConst() && b.isConst()) {
      return a == b;
    } else if( hasTerm( a ) && hasTerm( b ) ){
//      if( d_eqEngine->isTriggerTerm(a, THEORY_SETS) &&
//          d_eqEngine->isTriggerTerm(b, THEORY_SETS) ) {
//        // Get representative trigger terms
//          TNode x_shared = d_eqEngine->getTriggerTermRepresentative(a, THEORY_SETS);
//          TNode y_shared = d_eqEngine->getTriggerTermRepresentative(b, THEORY_SETS);
//          EqualityStatus eqStatusDomain = d_sets.d_valuation.getEqualityStatus(x_shared, y_shared);
//          switch (eqStatusDomain) {
//            case EQUALITY_TRUE_AND_PROPAGATED:
//              // Should have been propagated to us
//              Trace("rels-debug") << "EQUALITY_TRUE_AND_PROPAGATED ****  equality( a, b ) = true" << std::endl;
//              return true;
//              break;
//            case EQUALITY_TRUE:
//              // Missed propagation - need to add the pair so that theory engine can force propagation
//              Trace("rels-debug") << "EQUALITY_TRUE **** equality( a, b ) = true" << std::endl;
//              return true;
//              break;
//            case EQUALITY_FALSE_AND_PROPAGATED:
//              // Should have been propagated to us
//              Trace("rels-debug") << "EQUALITY_FALSE_AND_PROPAGATED ******** equality( a, b ) = false" << std::endl;
//              return false;
//              break;
//            case EQUALITY_FALSE:
//              Trace("rels-debug") << "EQUALITY_FALSE **** equality( a, b ) = false" << std::endl;
//              return false;
//              break;
//
//            default:
//              // Covers EQUALITY_TRUE_IN_MODEL (common case) and EQUALITY_UNKNOWN
//              break;
//          }
//      }
      return d_eqEngine->areEqual( a, b );
    } else {
      makeSharedTerm(a);
      makeSharedTerm(b);
      return false;
    }
  }

  bool TheorySetsRels::checkCycles(Node join_term) {
    return false;
  }

  bool TheorySetsRels::safeAddToMap(std::map< Node, std::vector<Node> >& map, Node rel_rep, Node member) {
    if(map.find(rel_rep) == map.end()) {
      std::vector<Node> members;
      members.push_back(member);
      map[rel_rep] = members;
      return true;
    } else if(std::find(map[rel_rep].begin(), map[rel_rep].end(), member) == map[rel_rep].end()) {
      map[rel_rep].push_back(member);
      return true;
    }
    return false;
  }

  void TheorySetsRels::addToMap(std::map< Node, std::vector<Node> >& map, Node rel_rep, Node member) {
    if(map.find(rel_rep) == map.end()) {
      std::vector<Node> members;
      members.push_back(member);
      map[rel_rep] = members;
    } else {
      map[rel_rep].push_back(member);
    }
  }

  inline Node TheorySetsRels::selectElement( Node tuple, int n_th ) {
    if(tuple.isConst() || (!tuple.isVar() && !tuple.isConst()))
      return tuple[n_th];
    Datatype dt = tuple.getType().getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, dt[0][n_th].getSelector(), tuple);
  }

  void TheorySetsRels::addSharedTerm( TNode n ) {
    Trace("rels-debug") << "[sets-rels] Add a shared term:  " << n << std::endl;
    d_sets.addSharedTerm(n);
    d_eqEngine->addTriggerTerm(n, THEORY_SETS);
  }

  bool TheorySetsRels::hasTuple( Node rel_rep, Node tuple ){
    if(d_membership_db.find(rel_rep) == d_membership_db.end())
      return false;
    return std::find(d_membership_db[rel_rep].begin(),
                     d_membership_db[rel_rep].end(), tuple) != d_membership_db[rel_rep].end();
  }

  void TheorySetsRels::makeSharedTerm( Node n ) {
    if(d_shared_terms.find(n) == d_shared_terms.end()) {
      Node skolem = NodeManager::currentNM()->mkSkolem( "sde", n.getType() );
      sendLemma(MEMBER(skolem, SINGLETON(n)), d_trueNode, "share-term");
      d_shared_terms.insert(n);
    }
  }

  bool TheorySetsRels::holds(Node node) {
    bool polarity = node.getKind() != kind::NOT;
    Node atom = polarity ? node : node[0];
    Node polarity_atom = polarity ? d_trueNode : d_falseNode;
    if(d_eqEngine->hasTerm(node)) {
      return areEqual(node, polarity_atom);
    } else {
      Node atom_mod = NodeManager::currentNM()->mkNode(atom.getKind(), getRepresentative(atom[0]),
                                                       getRepresentative(atom[1]) );
      if(d_eqEngine->hasTerm(atom_mod)) {
        return areEqual(node, polarity_atom);
      }
    }
    return false;
  }

  void TheorySetsRels::computeTupleReps( Node n ) {
    if( d_tuple_reps.find( n ) == d_tuple_reps.end() ){
      for( unsigned i = 0; i < n.getType().getTupleLength(); i++ ){
        d_tuple_reps[n].push_back( getRepresentative( selectElement(n, i) ) );
      }
    }
  }

  inline void TheorySetsRels::addToMembershipDB(Node rel, Node member, Node reasons) {
    addToMap(d_membership_db, rel, member);
    addToMap(d_membership_exp_db, rel, reasons);
    computeTupleReps(member);
    d_membership_trie[rel].addTerm(member, d_tuple_reps[member]);
  }

  void TheorySetsRels::reduceTupleVar(Node n) {
    if(d_symbolic_tuples.find(n) == d_symbolic_tuples.end()) {
      Trace("rels-debug") << "Reduce tuple var: " << n[0] << " to concrete one " << std::endl;
      std::vector<Node> tuple_elements;
      tuple_elements.push_back(Node::fromExpr((n[0].getType().getDatatype())[0].getConstructor()));
      for(unsigned int i = 0; i < n[0].getType().getTupleLength(); i++) {
        Node element = selectElement(n[0], i);
        makeSharedTerm(element);
        tuple_elements.push_back(element);
      }
      Node tuple_reduct = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, tuple_elements);
      tuple_reduct = MEMBER(tuple_reduct, n[1]);
      Node tuple_reduction_lemma = NodeManager::currentNM()->mkNode(kind::IFF, n, tuple_reduct);
      sendLemma(tuple_reduction_lemma, d_trueNode, "tuple-reduction");
      d_symbolic_tuples.insert(n);
    }
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
    d_lemma(u),
    d_shared_terms(u),
    d_eqEngine(eq),
    d_conflict(conflict)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TRANSCLOSURE);
  }

  TheorySetsRels::~TheorySetsRels() {}

  std::vector<Node> TupleTrie::findTerms( std::vector< Node >& reps, int argIndex ) {
    std::vector<Node> nodes;
    std::map< Node, TupleTrie >::iterator it;
    if( argIndex==(int)reps.size()-1 ){
      if(reps[argIndex].getKind() == kind::SKOLEM) {
        it = d_data.begin();
        while(it != d_data.end()) {
          nodes.push_back(it->first);
          it++;
        }
      }
      return nodes;
    }else{
      it = d_data.find( reps[argIndex] );
      if( it==d_data.end() ){
        return nodes;
      }else{
        return it->second.findTerms( reps, argIndex+1 );
      }
    }
  }

  Node TupleTrie::existsTerm( std::vector< Node >& reps, int argIndex ) {
    if( argIndex==(int)reps.size() ){
      if( d_data.empty() ){
        return Node::null();
      }else{
        return d_data.begin()->first;
      }
    }else{
      std::map< Node, TupleTrie >::iterator it = d_data.find( reps[argIndex] );
      if( it==d_data.end() ){
        return Node::null();
      }else{
        return it->second.existsTerm( reps, argIndex+1 );
      }
    }
  }

  bool TupleTrie::addTerm( Node n, std::vector< Node >& reps, int argIndex ){
    if( argIndex==(int)reps.size() ){
      if( d_data.empty() ){
        //store n in d_data (this should be interpretted as the "data" and not as a reference to a child)
        d_data[n].clear();
        return true;
      }else{
        return false;
      }
    }else{
      return d_data[reps[argIndex]].addTerm( n, reps, argIndex+1 );
    }
  }

  void TupleTrie::debugPrint( const char * c, Node n, unsigned depth ) {
    for( std::map< Node, TupleTrie >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      for( unsigned i=0; i<depth; i++ ){ Debug(c) << "  "; }
      Debug(c) << it->first << std::endl;
      it->second.debugPrint( c, n, depth+1 );
    }
  }

}
}
}














