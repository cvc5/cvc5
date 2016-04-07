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

typedef std::map<Node, std::map<kind::Kind_t, std::vector<Node> > >::iterator TERM_IT;
typedef std::map<Node, std::map<Node, std::hash_set<Node, NodeHashFunction> > >::iterator TC_IT;
typedef std::map<Node, std::vector<Node> >::iterator MEM_IT;
typedef std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator TC_PAIR_IT;

  void TheorySetsRels::check(Theory::Effort level) {
    Trace("rels") << "\n[sets-rels] ******************************* Start the relational solver *******************************\n" << std::endl;
    if(Theory::fullEffort(level)) {
      collectRelsInfo();
      check();
      doPendingLemmas();
      Assert(d_lemma_cache.empty());
      Assert(d_pending_facts.empty());
    } else {
      doPendingMerge();
    }
    Trace("rels") << "\n[sets-rels] ******************************* Done with the relational solver *******************************\n" << std::endl;
  }

  void TheorySetsRels::check() {
    MEM_IT m_it = d_membership_constraints_cache.begin();
    while(m_it != d_membership_constraints_cache.end()) {
      Node rel_rep = m_it->first;
      Trace("rels-debug") << "[sets-rels] Processing rel_rep = " << rel_rep << std::endl;

      // No relational terms found with rel_rep as its representative
      // But TRANSPOSE(rel_rep) may occur in the context
      if(d_terms_cache.find(rel_rep) == d_terms_cache.end()) {
        Node tp_rel = NodeManager::currentNM()->mkNode(kind::TRANSPOSE, rel_rep);
        Node tp_rel_rep = getRepresentative(tp_rel);
        if(d_terms_cache.find(tp_rel_rep) != d_terms_cache.end()) {
          for(unsigned int i = 0; i < m_it->second.size(); i++) {
//            Node exp = tp_rel == tp_rel_rep ? d_membership_exp_cache[rel_rep][i]
//                                            : AND(d_membership_exp_cache[rel_rep][i], EQUAL(tp_rel, tp_rel_rep));
            // Lazily apply transpose-occur rule.
            // Need to eagerly apply if we don't send facts as lemmas
            applyTransposeRule(d_membership_exp_cache[rel_rep][i], tp_rel_rep, true);
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
            // exp is a membership term and join_terms contains all
            // terms involving "join" operator that are in the same equivalence class with the right hand side of exp
            for(unsigned int j = 0; j < join_terms.size(); j++) {
              applyJoinRule(exp, join_terms[j]);
            }
          }
          if(kind_terms.find(kind::PRODUCT) != kind_terms.end()) {
            std::vector<Node> product_terms = kind_terms[kind::PRODUCT];
            for(unsigned int j = 0; j < product_terms.size(); j++) {
              applyProductRule(exp, product_terms[j]);
            }
          }
          if(kind_terms.find(kind::TRANSCLOSURE) != kind_terms.end()) {
            std::vector<Node> tc_terms = kind_terms[kind::TRANSCLOSURE];
            for(unsigned int j = 0; j < tc_terms.size(); j++) {
              applyTCRule(exp, tc_terms[j]);
            }
          }
        }
      }
      m_it++;
    }
    finalizeTCInfer();
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
              if(safeAddToMap(d_membership_constraints_cache, rel_rep, tup_rep)) {
                bool true_eq = areEqual(r, d_trueNode);
                Node reason = true_eq ? n : n.negate();
                addToMap(d_membership_exp_cache, rel_rep, reason);
                Trace("rels-mem") << "[******] exp: " << reason << " for " << rel_rep << std::endl;
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
            Node element = nthElementOfTuple(n, i);
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

  /*
   *
   *
   * transitive closure rule 1:   y = (TRANSCLOSURE x)
   *                           ---------------------------------------------
   *                              y = x | x.x | x.x.x | ... (| is union)
   *
   *
   *
   * transitive closure rule 2:   TRANSCLOSURE(x)
   *                            -----------------------------------------------------------
   *                              x <= TRANSCLOSURE(x) && (x JOIN x) <= TRANSCLOSURE(x) ....
   *
   *                              TC(x) = TC(y) => x = y
   *
   */

  void TheorySetsRels::buildTCGraph(Node tc_r_rep, Node tc_rep, Node tc_term) {
    std::map< Node, std::hash_set< Node, NodeHashFunction > > tc_graph;
    MEM_IT mem_it = d_membership_db.find(tc_r_rep);
    if(mem_it != d_membership_db.end()) {
      for(std::vector<Node>::iterator pair_it = mem_it->second.begin();
          pair_it != mem_it->second.end(); pair_it++) {
        TC_PAIR_IT pair_set_it = tc_graph.find(nthElementOfTuple(*pair_it, 0));
        if( pair_set_it != tc_graph.end() ) {
          pair_set_it->second.insert(nthElementOfTuple(*pair_it, 1));
        } else {
          std::hash_set< Node, NodeHashFunction > snd_pair_set;
          snd_pair_set.insert(nthElementOfTuple(*pair_it, 1));
          tc_graph[nthElementOfTuple(*pair_it, 0)] = snd_pair_set;
        }
      }
    }
    Node reason = getReason(tc_rep, tc_term, tc_r_rep, tc_term[0]);
    if(!reason.isNull()) {
      d_membership_tc_exp_cache[tc_rep] = reason;
    }
    d_membership_tc_cache[tc_rep] = tc_graph;
  }

  void TheorySetsRels::applyTCRule(Node exp, Node tc_term) {
    Trace("rels-debug") << "\n[sets-rels] *********** Applying TRANSITIVE CLOSURE rule on  "
                        << tc_term << " with explanation " << exp << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node tc_rep = getRepresentative(tc_term);
    Node tc_r_rep = getRepresentative(tc_term[0]);

    // build the TC graph for tc_rep if it was not created before
    if( d_membership_tc_cache.find(tc_rep) == d_membership_tc_cache.end() ) {
      buildTCGraph(tc_r_rep, tc_rep, tc_term);
    }
    // insert atom[0] in the tc_graph
    TC_IT tc_graph_it = d_membership_tc_cache.find(tc_rep);
    if(polarity) {
      if(tc_graph_it != d_membership_tc_cache.end()) {
        TC_PAIR_IT pair_set_it = tc_graph_it->second.find(nthElementOfTuple(atom[0], 0));
        if(pair_set_it != tc_graph_it->second.end()) {
          pair_set_it->second.insert(nthElementOfTuple(atom[0], 1));
        } else {
          std::hash_set< Node, NodeHashFunction > pair_set;
          pair_set.insert(nthElementOfTuple(atom[0], 1));
          tc_graph_it->second[nthElementOfTuple(atom[0], 0)] = pair_set;
        }
        Node reason = getReason(tc_rep, tc_term, tc_r_rep, tc_term[0]);
        std::map< Node, Node >::iterator exp_it = d_membership_tc_exp_cache.find(tc_rep);
        if(!reason.isNull() && exp_it->second != reason) {
          d_membership_tc_exp_cache[tc_rep] = Rewriter::rewrite(AND(exp_it->second, reason));
        }
      } else {
        std::map< Node, std::hash_set< Node, NodeHashFunction > > pair_set;
        std::hash_set< Node, NodeHashFunction > set;
        set.insert(nthElementOfTuple(atom[0], 1));
        pair_set[nthElementOfTuple(atom[0], 0)] = set;
        d_membership_tc_cache[tc_rep] = pair_set;
        Node reason = getReason(tc_rep, tc_term, tc_r_rep, tc_term[0]);
        if(!reason.isNull()) {
          d_membership_tc_exp_cache[tc_rep] = reason;
        }
      }
    // check if atom[0] exists in TC graph for conflict
    } else {
      if(tc_graph_it != d_membership_tc_cache.end()) {
        checkTCGraphForConflict(atom, tc_rep, d_trueNode, nthElementOfTuple(atom[0], 0),
                                nthElementOfTuple(atom[0], 1), tc_graph_it->second);
      }
    }
  }

  void TheorySetsRels::checkTCGraphForConflict (Node atom, Node tc_rep, Node exp, Node a, Node b,
                                                std::map< Node, std::hash_set< Node, NodeHashFunction > >& pair_set) {
    TC_PAIR_IT pair_set_it = pair_set.find(a);
    if(pair_set_it != pair_set.end()) {
      if(pair_set_it->second.find(b) != pair_set_it->second.end()) {
        Node reason = AND(exp, findMemExp(tc_rep, constructPair(tc_rep, a, b)));
        if(atom[1] != tc_rep) {
          reason = AND(exp, EQUAL(atom[1], tc_rep));
        }
        Trace("rels-debug") << "[sets-rels] found a conflict and send out lemma : "
                            <<  NodeManager::currentNM()->mkNode(kind::IMPLIES, reason, atom) << std::endl;
        d_sets_theory.d_out->lemma(NodeManager::currentNM()->mkNode(kind::IMPLIES, reason, atom));
//        Trace("rels-debug") << "[sets-rels] found a conflict and send out lemma : "
//                            << AND(reason.negate(), atom) << std::endl;
//        d_sets_theory.d_out->conflict(AND(reason.negate(), atom));
      } else {
        std::hash_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();
        while(set_it != pair_set_it->second.end()) {
          checkTCGraphForConflict(atom, tc_rep, AND(exp, findMemExp(tc_rep, constructPair(tc_rep, a, *set_it))),
                                  *set_it, b, pair_set);
          set_it++;
        }
      }
    }
  }


 /*  product-split rule:  (a, b) IS_IN (X PRODUCT Y)
  *                     ----------------------------------
  *                       a IS_IN X  && b IS_IN Y
  *
  *  product-compose rule: (a, b) IS_IN X    (c, d) IS_IN Y  NOT (r, s, t, u) IS_IN (X PRODUCT Y)
  *                        ----------------------------------------------------------------------
  *                                         (a, b, c, d) IS_IN (X PRODUCT Y)
  */

  void TheorySetsRels::applyProductRule(Node exp, Node product_term) {
    Trace("rels-debug") << "\n[sets-rels] *********** Applying PRODUCT rule  " << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node r1_rep = getRepresentative(product_term[0]);
    Node r2_rep = getRepresentative(product_term[1]);

    if(polarity) {
      Trace("rels-debug") << "\n[sets-rels] Apply PRODUCT-SPLIT rule on term: " << product_term
                          << " with explanation: " << exp << std::endl;
      std::vector<Node> r1_element;
      std::vector<Node> r2_element;

      NodeManager *nm = NodeManager::currentNM();
      Datatype dt = r1_rep.getType().getSetElementType().getDatatype();
      unsigned int i = 0;
      unsigned int s1_len = r1_rep.getType().getSetElementType().getTupleLength();
      unsigned int tup_len = product_term.getType().getSetElementType().getTupleLength();

      r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      for(; i < s1_len; ++i) {
        r1_element.push_back(nthElementOfTuple(atom[0], i));
      }

      dt = r2_rep.getType().getSetElementType().getDatatype();
      r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      for(; i < tup_len; ++i) {
        r2_element.push_back(nthElementOfTuple(atom[0], i));
      }

      Node fact;
      Node reason = exp;
      Node t1 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element));
      Node t2 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element));

      if(!hasMember(r1_rep, t1)) {
        fact = MEMBER( t1, r1_rep );
        if(r1_rep != product_term[0])
          reason = Rewriter::rewrite(AND(reason, EQUAL(r1_rep, product_term[0])));
        addToMap(d_membership_db, r1_rep, t1);
        addToMap(d_membership_exp_db, r1_rep, reason);
        sendInfer(fact, reason, "product-split");
      }

      if(!hasMember(r2_rep, t2)) {
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
                          << " with explanation: " << exp << std::endl;
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
    Trace("rels-debug") << "\n[sets-rels] *********** Applying JOIN rule  " << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node r1_rep = getRepresentative(join_term[0]);
    Node r2_rep = getRepresentative(join_term[1]);

    if(polarity) {

      Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN-SPLIT rule on term: " << join_term
                          << " with explanation: " << exp << std::endl;

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
        r1_element.push_back(nthElementOfTuple(atom[0], i));
      }
      r1_element.push_back(shared_x);

      dt = r2_rep.getType().getSetElementType().getDatatype();
      r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      r2_element.push_back(shared_x);
      for(; i < tup_len; ++i) {
        r2_element.push_back(nthElementOfTuple(atom[0], i));
      }

      Node t1 = nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element);
      Node t2 = nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element);
      computeTupleReps(t1);
      computeTupleReps(t2);
      std::vector<Node> elements = d_membership_trie[r1_rep].findTerms(d_tuple_reps[t1]);

      for(unsigned int j = 0; j < elements.size(); j++) {
        std::vector<Node> new_tup;
        new_tup.push_back(elements[j]);
        new_tup.insert(new_tup.end(), d_tuple_reps[t2].begin()+1, d_tuple_reps[t2].end());
        if(d_membership_trie[r2_rep].existsTerm(new_tup) != Node::null()) {
          return;
        }
      }

      Node fact;
      Node reason = atom[1] == join_term ? exp : AND(exp, explain(EQUAL(atom[1], join_term)));
      Node reasons = reason;

      fact = MEMBER(t1, r1_rep);
      if(r1_rep != join_term[0]) {
        reasons = Rewriter::rewrite(AND(reason, explain(EQUAL(r1_rep, join_term[0]))));
      }
      addToMembershipDB(r1_rep, t1, reasons);
      sendInfer(fact, reasons, "join-split");

      reasons = reason;
      fact = MEMBER(t2, r2_rep);
      if(r2_rep != join_term[1]) {
        reasons = Rewriter::rewrite(AND(reason, explain(EQUAL(r2_rep, join_term[1]))));
      }
      addToMembershipDB(r2_rep, t2, reasons);
      sendInfer(fact, reasons, "join-split");

      // Need to make the skolem "shared_x" as shared term
      makeSharedTerm(shared_x);
    } else {
      // ONLY need to explicitly compute joins if there are negative literals involving JOIN
      Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN-COMPOSE rule on term: " << join_term
                          << " with explanation: " << exp << std::endl;
      computeRels(join_term);
    }
  }

  /*
   * transpose-occur rule:   [NOT] (a, b) IS_IN X   (TRANSPOSE X) occurs
   *                         -------------------------------------------------------
   *                         [NOT] (b, a) IS_IN (TRANSPOSE X)
   *
   * transpose-reverse rule:    [NOT] (a, b) IS_IN (TRANSPOSE X)
   *                         ------------------------------------------------
   *                            [NOT] (b, a) IS_IN X
   *
   *
   * transpose-equal rule:   [NOT]  (TRANSPOSE X) = (TRANSPOSE Y)
   *                         -----------------------------------------------
   *                         [NOT]  (X = Y)
   */
  void TheorySetsRels::applyTransposeRule(Node exp, Node tp_term, bool tp_occur) {
    Trace("rels-debug") << "\n[sets-rels] *********** Applying TRANSPOSE rule  " << std::endl;
    bool polarity = exp.getKind() != kind::NOT;
    Node atom = polarity ? exp : exp[0];
    Node reversedTuple = getRepresentative(reverseTuple(atom[0]));

    if(tp_occur) {
      Trace("rels-debug") << "\n[sets-rels] Apply TRANSPOSE-OCCUR rule on term: " << tp_term
                             << " with explanation: " << exp << std::endl;
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

  // Todo: need to add equality between two pair's left and right elements as explanation
  void TheorySetsRels::inferTC( Node exp, Node tc_rep, std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph,
                                Node start_node, Node cur_node, std::hash_set< Node, NodeHashFunction >& elements, bool first_round ) {
    Node pair = constructPair(tc_rep, start_node, cur_node);
    if(safeAddToMap(d_membership_db, tc_rep, pair)) {
      addToMap(d_membership_exp_db, tc_rep, exp);
      sendLemma( MEMBER(pair, tc_rep), exp, "Transitivity" );
    }

    if(!first_round) {
      std::hash_set< Node, NodeHashFunction >::iterator ele_it = elements.begin();
      while(ele_it != elements.end()) {
        if(areEqual(cur_node, *ele_it)) {
          return;
        }
        ele_it++;
      }
    }
    std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator pair_set_it = tc_graph.begin();
    while(pair_set_it != tc_graph.end()) {
      if(areEqual(pair_set_it->first, cur_node)) {
        break;
      }
      pair_set_it++;
    }
    if(pair_set_it != tc_graph.end()) {
      for(std::hash_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();
          set_it != pair_set_it->second.end(); set_it++) {
        Node p = constructPair( tc_rep, cur_node, *set_it );
        Node reason = AND( findMemExp(tc_rep, p), exp );
        Assert(!reason.isNull());
        elements.insert(*set_it);
        inferTC( reason, tc_rep, tc_graph, start_node, *set_it, elements, false );
      }
    }
  }

  void TheorySetsRels::inferTC(Node tc_rep, std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph) {
    Trace("rels-debug") << "[sets-rels] Build TC graph for tc_rep = " << tc_rep << std::endl;
    for(std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator pair_set_it = tc_graph.begin();
        pair_set_it != tc_graph.end(); pair_set_it++) {
      for(std::hash_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();
          set_it != pair_set_it->second.end(); set_it++) {
        std::hash_set<Node, NodeHashFunction> elements;
        Node pair = constructPair(tc_rep, pair_set_it->first, *set_it);
        Node exp = findMemExp(tc_rep, pair);
        Trace("rels-debug") << "[sets-rels] pair = " << pair << std::endl;
        if(d_membership_tc_exp_cache.find(tc_rep) != d_membership_tc_exp_cache.end()) {
          exp = AND(d_membership_tc_exp_cache[tc_rep], exp);
        }
        Assert(!exp.isNull());
        elements.insert(pair_set_it->first);
        elements.insert(*set_it);
        inferTC( exp, tc_rep, tc_graph, pair_set_it->first, *set_it, elements, true );
      }
    }
  }

  void TheorySetsRels::finalizeTCInfer() {
    Trace("rels-debug") << "[sets-rels] Finalizing transitive closure inferences!" << std::endl;
    for(TC_IT tc_it = d_membership_tc_cache.begin(); tc_it != d_membership_tc_cache.end(); tc_it++) {
      inferTC(tc_it->first, tc_it->second);
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
    composeTupleMemForRels(n);
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
  void TheorySetsRels::composeTupleMemForRels( Node n ) {
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
        Node r2_lmost = nthElementOfTuple(r2_elements[j], 0);
        Node r1_rmost = nthElementOfTuple(r1_elements[i], t1_len-1);
        composed_tuple.push_back(Node::fromExpr(tn.getDatatype()[0].getConstructor()));

        if((areEqual(r1_rmost, r2_lmost) && n.getKind() == kind::JOIN) ||
            n.getKind() == kind::PRODUCT) {
          bool isProduct = n.getKind() == kind::PRODUCT;
          unsigned int k = 0;
          unsigned int l = 1;
          for(; k < t1_len - 1; ++k) {
            composed_tuple.push_back(nthElementOfTuple(r1_elements[i], k));
          }
          if(isProduct) {
            composed_tuple.push_back(nthElementOfTuple(r1_elements[i], k));
            composed_tuple.push_back(nthElementOfTuple(r2_elements[j], 0));
          }
          for(; l < t2_len; ++l) {
            composed_tuple.push_back(nthElementOfTuple(r2_elements[j], l));
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
        d_sets_theory.d_out->lemma( d_lemma_cache[i] );
//        d_sets_theory.d_out->conflict()
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
        d_sets_theory.d_out->lemma(NodeManager::currentNM()->mkNode(kind::IMPLIES, child_it->second, child_it->first));
      }
    }
    d_pending_facts.clear();
    d_membership_constraints_cache.clear();
    d_membership_tc_cache.clear();
    d_membership_tc_exp_cache.clear();
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
    d_membership_constraints_cache.clear();
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
      elements.push_back( nthElementOfTuple(tuple, i) );
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
    Trace("rels-debug") << "[sets-rels] areEqual( a = " << a << ", b = " << b << ")" << std::endl;
    if(a == b) {
      return true;
    } else if( hasTerm( a ) && hasTerm( b ) ){
      return d_eqEngine->areEqual( a, b );
    } else if(a.getType().isTuple()) {
      bool equal = true;
      for(unsigned int i = 0; i < a.getType().getTupleLength(); i++) {
        equal = equal && areEqual(nthElementOfTuple(a, i), nthElementOfTuple(b, i));
      }
      return equal;
    } else if(!a.getType().isBoolean()){
      makeSharedTerm(a);
      makeSharedTerm(b);
    }
    return false;
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

  inline Node TheorySetsRels::getReason(Node tc_rep, Node tc_term, Node tc_r_rep, Node tc_r) {
    if(tc_term != tc_rep) {
      Node reason = explain(EQUAL(tc_term, tc_rep));
      if(tc_term[0] != tc_r_rep) {
        return AND(reason, explain(EQUAL(tc_term[0], tc_r_rep)));
      }
    }
    return Node::null();
  }

  // tuple might be a member of tc_rep; or it might be a member of tc_terms
  Node TheorySetsRels::findMemExp(Node tc_rep, Node tuple) {
    Trace("rels-exp") << "TheorySetsRels::findMemExp ( tc_rep = " << tc_rep << ", tuple = " << tuple << ")" << std::endl;
    std::vector<Node> tc_terms = d_terms_cache.find(tc_rep)->second[kind::TRANSCLOSURE];
    Assert(tc_terms.size() > 0);
    for(unsigned int i = 0; i < tc_terms.size(); i++) {
      Node r_rep = getRepresentative(tc_terms[i][0]);
      Trace("rels-exp") << "TheorySetsRels::findMemExp ( r_rep = " << r_rep << ", tuple = " << tuple << ")" << std::endl;
      std::map< Node, std::vector< Node > >::iterator tc_r_mems = d_membership_db.find(r_rep);
      if(tc_r_mems != d_membership_db.end()) {
        for(unsigned int i = 0; i < tc_r_mems->second.size(); i++) {
          if(areEqual(tc_r_mems->second[i], tuple)) {
            return explain(d_membership_exp_db[r_rep][i]);
          }
        }
      }

      Node tc_term_rep = getRepresentative(tc_terms[i]);
      std::map< Node, std::vector< Node > >::iterator tc_t_mems = d_membership_db.find(tc_term_rep);
      Trace("rels-exp") << "TheorySetsRels::findMemExp ( tc_t_rep = " << tc_term_rep << ", tuple = " << tuple << ")" << std::endl;
      if(tc_t_mems != d_membership_db.end()) {
        for(unsigned int i = 0; i < tc_t_mems->second.size(); i++) {
          if(areEqual(tc_t_mems->second[i], tuple)) {
            return explain(d_membership_exp_db[tc_term_rep][i]);
          }
        }
      }
    }
//    std::map< Node, std::vector< Node > >::iterator tc_mems = d_membership_db.find(tc_rep);
//    if(tc_mems != d_membership_db.end()) {
//      for(unsigned int i = 0; i < tc_mems->second.size(); i++) {
//        if(tc_mems->second[i] == tuple) {
//          return explain(d_membership_exp_db[tc_rep][i]);
//        }
//      }
//    }
    return Node::null();
  }

  inline Node TheorySetsRels::nthElementOfTuple( Node tuple, int n_th ) {
    if(tuple.isConst() || (!tuple.isVar() && !tuple.isConst()))
      return tuple[n_th];
    Datatype dt = tuple.getType().getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, dt[0][n_th].getSelector(), tuple);
  }

  void TheorySetsRels::addSharedTerm( TNode n ) {
    Trace("rels-debug") << "[sets-rels] Add a shared term:  " << n << std::endl;
    d_sets_theory.addSharedTerm(n);
    d_eqEngine->addTriggerTerm(n, THEORY_SETS);
  }

  bool TheorySetsRels::hasMember( Node rel_rep, Node tuple ){
    if(d_membership_db.find(rel_rep) == d_membership_db.end())
      return false;
    return std::find(d_membership_db[rel_rep].begin(),
                     d_membership_db[rel_rep].end(), tuple) != d_membership_db[rel_rep].end();
  }

  void TheorySetsRels::makeSharedTerm( Node n ) {
    if(d_shared_terms.find(n) == d_shared_terms.end() && !n.getType().isBoolean()) {
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
      Node atom_mod = NodeManager::currentNM()->mkNode(atom.getKind(),
                                                       getRepresentative(atom[0]),
                                                       getRepresentative(atom[1]));
      if(d_eqEngine->hasTerm(atom_mod)) {
        return areEqual(node, polarity_atom);
      }
    }
    return false;
  }

  void TheorySetsRels::computeTupleReps( Node n ) {
    if( d_tuple_reps.find( n ) == d_tuple_reps.end() ){
      for( unsigned i = 0; i < n.getType().getTupleLength(); i++ ){
        d_tuple_reps[n].push_back( getRepresentative( nthElementOfTuple(n, i) ) );
      }
    }
  }

  inline void TheorySetsRels::addToMembershipDB(Node rel, Node member, Node reasons) {
    addToMap(d_membership_db, rel, member);
    addToMap(d_membership_exp_db, rel, reasons);
    computeTupleReps(member);
    d_membership_trie[rel].addTerm(member, d_tuple_reps[member]);
  }

  inline Node TheorySetsRels::constructPair(Node tc_rep, Node a, Node b) {
    Datatype dt = tc_rep.getType().getSetElementType().getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, Node::fromExpr(dt[0].getConstructor()), a, b);
  }

  void TheorySetsRels::reduceTupleVar(Node n) {
    if(d_symbolic_tuples.find(n) == d_symbolic_tuples.end()) {
      Trace("rels-debug") << "Reduce tuple var: " << n[0] << " to concrete one " << std::endl;
      std::vector<Node> tuple_elements;
      tuple_elements.push_back(Node::fromExpr((n[0].getType().getDatatype())[0].getConstructor()));
      for(unsigned int i = 0; i < n[0].getType().getTupleLength(); i++) {
        Node element = nthElementOfTuple(n[0], i);
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
    d_c(c),
    d_sets_theory(d_set),
    d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
    d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
    d_pending_merge(c),
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

  Node TheorySetsRels::explain(Node literal)
  {
    Trace("rels-debug") << "[sets-rels] TheorySetsRels::explain(" << literal << ")"<< std::endl;

    bool polarity = literal.getKind() != kind::NOT;
    TNode atom = polarity ? literal : literal[0];
    std::vector<TNode> assumptions;

    if(atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
      d_eqEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
    } else if(atom.getKind() == kind::MEMBER) {
      if( !d_eqEngine->hasTerm(atom)) {
        d_eqEngine->addTerm(atom);
      }
      d_eqEngine->explainPredicate(atom, polarity, assumptions);
    } else {
      Trace("rels-debug") << "unhandled: " << literal << "; (" << atom << ", "
                    << polarity << "); kind" << atom.getKind() << std::endl;
      Unhandled();
    }
    Trace("rels-debug") << "[sets-rels] ****** done with TheorySetsRels::explain(" << literal << ")"<< std::endl;
    return mkAnd(assumptions);
  }

  TheorySetsRels::EqcInfo::EqcInfo( context::Context* c ) :
  d_mem(c), d_not_mem(c), d_tp(c), d_pt(c) {}

  void TheorySetsRels::eqNotifyNewClass( Node n ) {
    Trace("rels-std") << "[sets-rels] eqNotifyNewClass:" << " t = " << n << std::endl;
    if(isRel(n) && (n.getKind() == kind::TRANSPOSE || n.getKind() == kind::PRODUCT)) {
      getOrMakeEqcInfo( n, true );
    }
  }

  void TheorySetsRels::eqNotifyPostMerge( Node t1, Node t2 ) {
    Trace("rels-std") << "[sets-rels] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;

    // Merge membership constraint with "true" or "false" eqc
    // Todo: t1 might not be "true" or "false" rep
    if((t1 == d_trueNode || t1 == d_falseNode) &&
        t2.getKind() == kind::MEMBER &&
        t2[0].getType().isTuple()) {

      Assert(t1 == d_trueNode || t1 == d_falseNode);
      bool polarity = t1 == d_trueNode;
      Node t2_1rep = getRepresentative(t2[1]);
      EqcInfo* ei = getOrMakeEqcInfo( t2_1rep );

      if(ei == NULL) {
        ei = getOrMakeEqcInfo( t2_1rep, true );
      }
      // might not need to store the membership info
      // if we don't need to consider the eqc merge?
      if(polarity) {
        ei->d_mem.insert(t2[0]);
      } else {
        ei->d_not_mem.insert(t2[0]);
      }
      if(!ei->d_tp.get().isNull()) {
        Node exp = polarity ? explain(t2) : explain(t2.negate());
        if(ei->d_tp.get() != t2[1]) {
          exp = AND( explain(EQUAL( ei->d_tp.get(), t2[1]) ), exp );
        }
        sendInferTranspose( polarity, t2[0], ei->d_tp.get(), exp, true );
      }
      if(!ei->d_pt.get().isNull()) {
        Node exp = polarity ? explain(t2) : explain(t2.negate());
        if(ei->d_pt.get() != t2[1]) {
          exp = AND( explain(EQUAL( ei->d_pt.get(), t2[1]) ), exp );
        }
        sendInferProduct(polarity, t2[0], ei->d_pt.get(), exp);
      }
    // Merge two relation eqcs
    } else if(t1.getType().isSet() &&
              t2.getType().isSet() &&
              t1.getType().getSetElementType().isTuple()) {
      mergeTransposeEqcs(t1, t2);
      mergeProductEqcs(t1, t2);
    }

    Trace("rels-std") << "[sets-rels] done with eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  }

  void TheorySetsRels::mergeProductEqcs(Node t1, Node t2) {
    EqcInfo* t1_ei = getOrMakeEqcInfo(t1);
    EqcInfo* t2_ei = getOrMakeEqcInfo(t2);
    if(t1_ei != NULL && t2_ei != NULL) {
      // PT(t1) = PT(t2) -> t1 = t2;
      if(!t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull()) {
        sendInferProduct( true, t1_ei->d_pt.get(), t2_ei->d_pt.get(), explain(EQUAL(t1, t2)) );
      }
      // Apply Product rule on (non)members of t2 and t1->tp
      if(!t1_ei->d_pt.get().isNull()) {
        for(NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++) {
          if(!t1_ei->d_mem.contains(*itr)) {
            sendInferProduct( true, *itr, t1_ei->d_pt.get(), AND(explain(EQUAL(t1_ei->d_pt.get(), t2)), explain(MEMBER(*itr, t2))) );
          }
        }
        for(NodeSet::key_iterator itr = t2_ei->d_not_mem.key_begin(); itr != t2_ei->d_not_mem.key_end(); itr++) {
          if(!t1_ei->d_not_mem.contains(*itr)) {
            sendInferProduct( false, *itr, t1_ei->d_pt.get(), AND(explain(EQUAL(t1_ei->d_pt.get(), t2)), explain(MEMBER(*itr, t2).negate())) );
          }
        }
        // Apply transpose rule on (non)members of t1 and t2->tp
      } else if(!t2_ei->d_pt.get().isNull()) {
        t1_ei->d_pt.set(t2_ei->d_pt);
        for(NodeSet::key_iterator itr = t1_ei->d_mem.key_begin(); itr != t1_ei->d_mem.key_end(); itr++) {
          if(!t2_ei->d_mem.contains(*itr)) {
            sendInferProduct( true, *itr, t2_ei->d_pt.get(), AND(explain(EQUAL(t1, t2_ei->d_pt.get())), explain(MEMBER(*itr, t1))) );
          }
        }
        for(NodeSet::key_iterator itr = t1_ei->d_not_mem.key_begin(); itr != t1_ei->d_not_mem.key_end(); itr++) {
          if(!t2_ei->d_not_mem.contains(*itr)) {
            sendInferProduct( false, *itr, t2_ei->d_pt.get(), AND(explain(EQUAL(t1, t2_ei->d_pt.get())), explain(MEMBER(*itr, t1).negate())) );
          }
        }
      }
    // t1 was created already and t2 was not
    } else if(t1_ei != NULL) {
      if(t1_ei->d_pt.get().isNull() && t2.getKind() == kind::PRODUCT) {
        t1_ei->d_pt.set( t2 );
      }
    } else if(t2_ei != NULL){
      t1_ei = getOrMakeEqcInfo(t1, true);
      for(NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++) {
        t1_ei->d_mem.insert(*itr);
      }
      for(NodeSet::key_iterator itr = t2_ei->d_not_mem.key_begin(); itr != t2_ei->d_not_mem.key_end(); itr++) {
        t1_ei->d_not_mem.insert(*itr);
      }
      if(t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull()) {
        t1_ei->d_pt.set(t2_ei->d_pt);
      }
    }
  }

  void TheorySetsRels::mergeTransposeEqcs(Node t1, Node t2) {
    EqcInfo* t1_ei = getOrMakeEqcInfo(t1);
    EqcInfo* t2_ei = getOrMakeEqcInfo(t2);
    if(t1_ei != NULL && t2_ei != NULL) {
      // TP(t1) = TP(t2) -> t1 = t2;
      if(!t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull()) {
        sendInferTranspose( true, t1_ei->d_tp.get(), t2_ei->d_tp.get(), explain(EQUAL(t1, t2)) );
      }
      // Apply transpose rule on (non)members of t2 and t1->tp
      if(!t1_ei->d_tp.get().isNull()) {
        for(NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++) {
          if(!t1_ei->d_mem.contains(*itr)) {
            sendInferTranspose( true, *itr, t1_ei->d_tp.get(), AND(explain(EQUAL(t1_ei->d_tp.get(), t2)), explain(MEMBER(*itr, t2))) );
          }
        }
        for(NodeSet::key_iterator itr = t2_ei->d_not_mem.key_begin(); itr != t2_ei->d_not_mem.key_end(); itr++) {
          if(!t1_ei->d_not_mem.contains(*itr)) {
            sendInferTranspose( false, *itr, t1_ei->d_tp.get(), AND(explain(EQUAL(t1_ei->d_tp.get(), t2)), explain(MEMBER(*itr, t2).negate())) );
          }
        }
        // Apply transpose rule on (non)members of t1 and t2->tp
      } else if(!t2_ei->d_tp.get().isNull()) {
        t1_ei->d_tp.set(t2_ei->d_tp);
        for(NodeSet::key_iterator itr = t1_ei->d_mem.key_begin(); itr != t1_ei->d_mem.key_end(); itr++) {
          if(!t2_ei->d_mem.contains(*itr)) {
            sendInferTranspose( true, *itr, t2_ei->d_tp.get(), AND(explain(EQUAL(t1, t2_ei->d_tp.get())), explain(MEMBER(*itr, t1))) );
          }
        }
        for(NodeSet::key_iterator itr = t1_ei->d_not_mem.key_begin(); itr != t1_ei->d_not_mem.key_end(); itr++) {
          if(!t2_ei->d_not_mem.contains(*itr)) {
            sendInferTranspose( false, *itr, t2_ei->d_tp.get(), AND(explain(EQUAL(t1, t2_ei->d_tp.get())), explain(MEMBER(*itr, t1).negate())) );
          }
        }
      }
    // t1 was created already and t2 was not
    } else if(t1_ei != NULL) {
      if(t1_ei->d_tp.get().isNull() && t2.getKind() == kind::TRANSPOSE) {
        t1_ei->d_tp.set( t2 );
      }
    } else if(t2_ei != NULL){
      t1_ei = getOrMakeEqcInfo(t1, true);
      for(NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++) {
        t1_ei->d_mem.insert(*itr);
      }
      for(NodeSet::key_iterator itr = t2_ei->d_not_mem.key_begin(); itr != t2_ei->d_not_mem.key_end(); itr++) {
        t1_ei->d_not_mem.insert(*itr);
      }
      if(t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull()) {
        t1_ei->d_tp.set(t2_ei->d_tp);
      }
    }
  }

  void TheorySetsRels::doPendingMerge() {
    for(NodeList::const_iterator itr = d_pending_merge.begin(); itr != d_pending_merge.end(); itr++) {
      Trace("rels-std") << "[sets-rels-lemma] Process pending merge fact : "
                        << *itr << std::endl;
      d_sets_theory.d_out->lemma(*itr);
    }
  }

  void TheorySetsRels::sendInferTranspose( bool polarity, Node t1, Node t2, Node exp, bool reverseOnly ) {
    Assert(t2.getKind() == kind::TRANSPOSE);
    if(polarity && isRel(t1) && isRel(t2)) {
      Assert(t1.getKind() == kind::TRANSPOSE);
      Node n = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, EQUAL(t1[0], t2[0]) );
      Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying transpose rule: "
                        << n << std::endl;
      d_pending_merge.push_back(n);
      d_lemma.insert(n);
      return;
    }

    Node n1;
    if(reverseOnly) {
      if(polarity) {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(reverseTuple(t1), t2[0]) );
      } else {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(reverseTuple(t1), t2[0]).negate() );
      }
    } else {
      Node n2;
      if(polarity) {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(t1, t2) );
        n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(reverseTuple(t1), t2[0]) );
      } else {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(t1, t2).negate() );
        n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(reverseTuple(t1), t2[0]).negate() );
      }
      Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying transpose rule: "
                        << n2 << std::endl;
      d_pending_merge.push_back(n2);
      d_lemma.insert(n2);
    }
    Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying transpose rule: "
                      << n1 << std::endl;
    d_pending_merge.push_back(n1);
    d_lemma.insert(n1);

  }

  void TheorySetsRels::sendInferProduct( bool polarity, Node t1, Node t2, Node exp ) {
    Assert(t2.getKind() == kind::PRODUCT);
    if(polarity && isRel(t1) && isRel(t2)) {
      Assert(t1.getKind() == kind::PRODUCT);
      Node n = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, EQUAL(t1[0], t2[0]) );
      Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying transpose rule: "
                        << n << std::endl;
      d_pending_merge.push_back(n);
      d_lemma.insert(n);
      return;
    }

    std::vector<Node> r1_element;
    std::vector<Node> r2_element;
    Node r1 = t2[0];
    Node r2 = t2[1];

    NodeManager *nm = NodeManager::currentNM();
    Datatype dt = r1.getType().getSetElementType().getDatatype();
    unsigned int i = 0;
    unsigned int s1_len = r1.getType().getSetElementType().getTupleLength();
    unsigned int tup_len = t2.getType().getSetElementType().getTupleLength();

    r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < s1_len; ++i) {
      r1_element.push_back(nthElementOfTuple(t1, i));
    }

    dt = r2.getType().getSetElementType().getDatatype();
    r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < tup_len; ++i) {
      r2_element.push_back(nthElementOfTuple(t1, i));
    }
    Node tuple_1 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element));
    Node tuple_2 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element));
    Node n1;
    Node n2;
    if(polarity) {
      n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_1, r1) );
      n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_2, r2) );
    } else {
      n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_1, r1).negate() );
      n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_2, r2).negate() );
    }
    Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying product rule: "
                      << n2 << std::endl;
    d_pending_merge.push_back(n2);
    d_lemma.insert(n2);
    Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying product rule: "
                      << n1 << std::endl;
    d_pending_merge.push_back(n1);
    d_lemma.insert(n1);

  }

  TheorySetsRels::EqcInfo* TheorySetsRels::getOrMakeEqcInfo( Node n, bool doMake ){
    std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
    if(eqc_i == d_eqc_info.end()){
      if( doMake ){
        EqcInfo* ei;
        if(eqc_i!=d_eqc_info.end()){
          ei = eqc_i->second;
        }else{
          ei = new EqcInfo(d_sets_theory.getSatContext());
          d_eqc_info[n] = ei;
        }
        if(n.getKind() == kind::TRANSPOSE){
          ei->d_tp = n;
        } else if(n.getKind() == kind::PRODUCT) {
          ei->d_pt = n;
        }
        return ei;
      }else{
        return NULL;
      }
    }else{
      return (*eqc_i).second;
    }
  }


  Node TheorySetsRels::mkAnd( std::vector<TNode>& conjunctions ) {
    Assert(conjunctions.size() > 0);
    std::set<TNode> all;

    for (unsigned i = 0; i < conjunctions.size(); ++i) {
      TNode t = conjunctions[i];
      if (t.getKind() == kind::AND) {
        for(TNode::iterator child_it = t.begin();
            child_it != t.end(); ++child_it) {
          Assert((*child_it).getKind() != kind::AND);
          all.insert(*child_it);
        }
      }
      else {
        all.insert(t);
      }
    }

    Assert(all.size() > 0);

    if (all.size() == 1) {
      // All the same, or just one
      return conjunctions[0];
    }

    NodeBuilder<> conjunction(kind::AND);
    std::set<TNode>::const_iterator it = all.begin();
    std::set<TNode>::const_iterator it_end = all.end();
    while (it != it_end) {
      conjunction << *it;
      ++ it;
    }

    return conjunction;
  }/* mkAnd() */

}
}
}














