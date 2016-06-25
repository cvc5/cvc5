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

typedef std::map<Node, std::map<kind::Kind_t, std::vector<Node> > >::iterator                   TERM_IT;
typedef std::map<Node, std::map<Node, std::hash_set<Node, NodeHashFunction> > >::iterator       TC_IT;
typedef std::map<Node, std::vector<Node> >::iterator                                            MEM_IT;
typedef std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator                     TC_PAIR_IT;

int TheorySetsRels::EqcInfo::counter        = 0;

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
      doPendingLemmas();
    }
    Trace("rels") << "\n[sets-rels] ******************************* Done with the relational solver *******************************\n" << std::endl;
  }

  void TheorySetsRels::check() {
    MEM_IT m_it = d_membership_constraints_cache.begin();
    while(m_it != d_membership_constraints_cache.end()) {
      Node rel_rep = m_it->first;

      // No relational terms found with rel_rep as its representative
      // But TRANSPOSE(rel_rep) may occur in the context
      if(d_terms_cache.find(rel_rep) == d_terms_cache.end()) {
        Node tp_rel     = NodeManager::currentNM()->mkNode(kind::TRANSPOSE, rel_rep);
        Node tp_rel_rep = getRepresentative(tp_rel);

        if(d_terms_cache.find(tp_rel_rep) != d_terms_cache.end()) {
          for(unsigned int i = 0; i < m_it->second.size(); i++) {
            // Lazily apply transpose-occur rule.
            // Need to eagerly apply if we don't send facts as lemmas
            applyTransposeRule(d_membership_exp_cache[rel_rep][i], tp_rel_rep, true);
          }
        }
      } else {
        for(unsigned int i = 0; i < m_it->second.size(); i++) {
          Node                                          exp             = d_membership_exp_cache[rel_rep][i];
          std::map<kind::Kind_t, std::vector<Node> >    kind_terms      = d_terms_cache[rel_rep];
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
          if(kind_terms.find(kind::TCLOSURE) != kind_terms.end()) {
            std::vector<Node> tc_terms = kind_terms[kind::TCLOSURE];
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
      Node                      r       = (*eqcs_i);
      eq::EqClassIterator       eqc_i   = eq::EqClassIterator( r, d_eqEngine );
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
                bool true_eq    = areEqual(r, d_trueNode);
                Node reason     = true_eq ? n : n.negate();

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
              n.getKind() == kind::TCLOSURE ) {
            std::map<kind::Kind_t, std::vector<Node> >  rel_terms;
            std::vector<Node>                           terms;
            // No r record is found
            if( d_terms_cache.find(r) == d_terms_cache.end() ) {
              terms.push_back(n);
              rel_terms[n.getKind()]    = terms;
              d_terms_cache[r]          = rel_terms;
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
            Node element = RelsUtils::nthElementOfTuple(n, i);

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
   * transitive closure rule 1:   y = (TCLOSURE x)
   *                           ---------------------------------------------
   *                              y = x | x.x | x.x.x | ... (| is union)
   *
   *
   *
   * transitive closure rule 2:   TCLOSURE(x)
   *                            -----------------------------------------------------------
   *                              x <= TCLOSURE(x) && (x JOIN x) <= TCLOSURE(x) ....
   *
   *                              TC(x) = TC(y) => x = y ?
   *
   */

  void TheorySetsRels::buildTCGraph(Node tc_r_rep, Node tc_rep, Node tc_term) {
    std::map< Node, std::hash_set< Node, NodeHashFunction > > tc_graph;
    MEM_IT mem_it = d_membership_db.find(tc_r_rep);

    if(mem_it != d_membership_db.end()) {
      for(std::vector<Node>::iterator pair_it = mem_it->second.begin();
          pair_it != mem_it->second.end(); pair_it++) {
        Node            fst_rep         = getRepresentative(RelsUtils::nthElementOfTuple(*pair_it, 0));
        Node            snd_rep         = getRepresentative(RelsUtils::nthElementOfTuple(*pair_it, 1));
        TC_PAIR_IT      pair_set_it     = tc_graph.find(fst_rep);

        if( pair_set_it != tc_graph.end() ) {
          pair_set_it->second.insert(snd_rep);
        } else {
          std::hash_set< Node, NodeHashFunction > snd_set;
          snd_set.insert(snd_rep);
          tc_graph[fst_rep] = snd_set;
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
    bool polarity       = exp.getKind() != kind::NOT;
    Node atom           = polarity ? exp : exp[0];
    Node tup_rep        = getRepresentative(atom[0]);
    Node tc_rep         = getRepresentative(tc_term);
    Node tc_r_rep       = getRepresentative(tc_term[0]);

    // build the TC graph for tc_rep if it was not created before
    if( d_rel_nodes.find(tc_rep) == d_rel_nodes.end() ) {
      Trace("rels-debug") << "[sets-rels]  Start building the TC graph!" << std::endl;
      buildTCGraph(tc_r_rep, tc_rep, tc_term);
      d_rel_nodes.insert(tc_rep);
    }

    // insert tup_rep in the tc_graph if it is not in the graph already
    TC_IT tc_graph_it = d_membership_tc_cache.find(tc_rep);

    if(polarity) {
      Node fst_rep = getRepresentative(RelsUtils::nthElementOfTuple(tup_rep, 0));
      Node snd_rep = getRepresentative(RelsUtils::nthElementOfTuple(tup_rep, 1));

      if(tc_graph_it != d_membership_tc_cache.end()) {
        TC_PAIR_IT pair_set_it = tc_graph_it->second.find(fst_rep);

        if(pair_set_it != tc_graph_it->second.end()) {
          pair_set_it->second.insert(snd_rep);
        } else {
          std::hash_set< Node, NodeHashFunction > pair_set;
          pair_set.insert(snd_rep);
          tc_graph_it->second[fst_rep] = pair_set;
        }

        Node                                    reason = getReason(tc_rep, tc_term, tc_r_rep, tc_term[0]);
        std::map< Node, Node >::iterator        exp_it = d_membership_tc_exp_cache.find(tc_rep);

        if(!reason.isNull() && exp_it->second != reason) {
          d_membership_tc_exp_cache[tc_rep] = Rewriter::rewrite(AND(exp_it->second, reason));
        }
      } else {
        std::map< Node, std::hash_set< Node, NodeHashFunction > >       pair_set;
        std::hash_set< Node, NodeHashFunction >                         snd_set;

        snd_set.insert(snd_rep);
        pair_set[fst_rep]               = snd_set;
        d_membership_tc_cache[tc_rep]   = pair_set;
        Node reason = getReason(tc_rep, tc_term, tc_r_rep, tc_term[0]);

        if(!reason.isNull()) {
          d_membership_tc_exp_cache[tc_rep] = reason;
        }
      }
    // check if tup_rep already exists in TC graph for conflict
    } else {
      if(tc_graph_it != d_membership_tc_cache.end()) {
        checkTCGraphForConflict(atom, tc_rep, d_trueNode, RelsUtils::nthElementOfTuple(tup_rep, 0),
                                RelsUtils::nthElementOfTuple(tup_rep, 1), tc_graph_it->second);
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
          reason = AND(exp, explain(EQUAL(atom[1], tc_rep)));
        }
        Trace("rels-debug") << "[sets-rels] found a conflict and send out lemma : "
                            <<  NodeManager::currentNM()->mkNode(kind::IMPLIES, Rewriter::rewrite(reason), atom) << std::endl;
        d_sets_theory.d_out->lemma(NodeManager::currentNM()->mkNode(kind::IMPLIES, Rewriter::rewrite(reason), atom));
//        Trace("rels-debug") << "[sets-rels] found a conflict and send out lemma : "
//                            << AND(reason.negate(), atom) << std::endl;
//        d_sets_theory.d_out->conflict(AND(reason.negate(), atom));
      } else {
        std::hash_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();

        while(set_it != pair_set_it->second.end()) {
          // need to check if *set_it has been looked already
          if(!areEqual(*set_it, a)) {
            checkTCGraphForConflict(atom, tc_rep, AND(exp, findMemExp(tc_rep, constructPair(tc_rep, a, *set_it))),
                                    *set_it, b, pair_set);  
          }
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

    if(d_rel_nodes.find(product_term) == d_rel_nodes.end()) {
      computeRels(product_term);
      d_rel_nodes.insert(product_term);
    }
    bool polarity       = exp.getKind() != kind::NOT;
    Node atom           = polarity ? exp : exp[0];
    Node r1_rep         = getRepresentative(product_term[0]);
    Node r2_rep         = getRepresentative(product_term[1]);

    Trace("rels-debug") << "\n[sets-rels] Apply PRODUCT-SPLIT rule on term: " << product_term
                        << " with explanation: " << exp << std::endl;
    std::vector<Node>   r1_element;
    std::vector<Node>   r2_element;
    NodeManager         *nm     = NodeManager::currentNM();
    Datatype            dt      = r1_rep.getType().getSetElementType().getDatatype();
    unsigned int        i       = 0;
    unsigned int        s1_len  = r1_rep.getType().getSetElementType().getTupleLength();
    unsigned int        tup_len = product_term.getType().getSetElementType().getTupleLength();

    r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < s1_len; ++i) {
      r1_element.push_back(RelsUtils::nthElementOfTuple(atom[0], i));
    }

    dt = r2_rep.getType().getSetElementType().getDatatype();
    r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < tup_len; ++i) {
      r2_element.push_back(RelsUtils::nthElementOfTuple(atom[0], i));
    }

    Node fact_1;
    Node fact_2;
    Node reason_1       = exp;
    Node reason_2       = exp;
    Node t1             = nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element);
    Node t1_rep         = getRepresentative(t1);
    Node t2             = nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element);
    Node t2_rep         = getRepresentative(t2);

    fact_1 = MEMBER( t1, r1_rep );
    fact_2 = MEMBER( t2, r2_rep );
    if(r1_rep != product_term[0]) {
      reason_1 = AND(reason_1, explain(EQUAL(r1_rep, product_term[0])));
    }
    if(t1 != t1_rep) {
      reason_1 = Rewriter::rewrite(AND(reason_1, explain(EQUAL(t1, t1_rep))));
    }
    if(r2_rep != product_term[1]) {
      reason_2 = AND(reason_2, explain(EQUAL(r2_rep, product_term[1])));
    }
    if(t2 != t2_rep) {
      reason_2 = Rewriter::rewrite(AND(reason_2, explain(EQUAL(t2, t2_rep))));
    }
    if(polarity) {
      sendInfer(fact_1, reason_1, "product-split");
      sendInfer(fact_2, reason_2, "product-split");
    } else {
      sendInfer(fact_1.negate(), reason_1, "product-split");
      sendInfer(fact_2.negate(), reason_2, "product-split");

      // ONLY need to explicitly compute joins if there are negative literals involving PRODUCT
      Trace("rels-debug") << "\n[sets-rels] Apply PRODUCT-COMPOSE rule on term: " << product_term
                          << " with explanation: " << exp << std::endl;
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
    if(d_rel_nodes.find(join_term) == d_rel_nodes.end()) {
      computeRels(join_term);
      d_rel_nodes.insert(join_term);
    }

    bool polarity       = exp.getKind() != kind::NOT;
    Node atom           = polarity ? exp : exp[0];
    Node r1_rep         = getRepresentative(join_term[0]);
    Node r2_rep         = getRepresentative(join_term[1]);

    if(polarity) {

      Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN-SPLIT rule on term: " << join_term
                          << " with explanation: " << exp << std::endl;

      std::vector<Node> r1_element;
      std::vector<Node> r2_element;
      NodeManager       *nm             = NodeManager::currentNM();
      TypeNode          shared_type     = r2_rep.getType().getSetElementType().getTupleTypes()[0];
      Node              shared_x        = nm->mkSkolem("sde_", shared_type);
      Datatype          dt              = r1_rep.getType().getSetElementType().getDatatype();
      unsigned int      i               = 0;
      unsigned int      s1_len          = r1_rep.getType().getSetElementType().getTupleLength();
      unsigned int      tup_len         = join_term.getType().getSetElementType().getTupleLength();

      r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      for(; i < s1_len-1; ++i) {
        r1_element.push_back(RelsUtils::nthElementOfTuple(atom[0], i));
      }

      r1_element.push_back(shared_x);
      dt = r2_rep.getType().getSetElementType().getDatatype();
      r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
      r2_element.push_back(shared_x);

      for(; i < tup_len; ++i) {
        r2_element.push_back(RelsUtils::nthElementOfTuple(atom[0], i));
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
      Node reason       = atom[1] == join_term ? exp : AND(exp, explain(EQUAL(atom[1], join_term)));
      Node reasons      = reason;

      fact = MEMBER(t1, r1_rep);
      if(r1_rep != join_term[0]) {
        reasons = Rewriter::rewrite(AND(reason, explain(EQUAL(r1_rep, join_term[0]))));
      }    
      sendInfer(fact, reasons, "join-split");

      reasons   = reason;
      fact      = MEMBER(t2, r2_rep);

      if(r2_rep != join_term[1]) {
        reasons = Rewriter::rewrite(AND(reason, explain(EQUAL(r2_rep, join_term[1]))));
      }
      sendInfer(fact, reasons, "join-split");

      // Need to make the skolem "shared_x" as shared term
      makeSharedTerm(shared_x);
    } else {
      // ONLY need to explicitly compute joins if there are negative literals involving JOIN
      Trace("rels-debug") <<  "\n[sets-rels] Apply JOIN-COMPOSE rule on term: " << join_term
                          << " with explanation: " << exp << std::endl;
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
    bool polarity       = exp.getKind() != kind::NOT;
    Node atom           = polarity ? exp : exp[0];
    Node reversedTuple  = getRepresentative(RelsUtils::reverseTuple(atom[0]));

    if(tp_occur) {
      Trace("rels-debug") << "\n[sets-rels] Apply TRANSPOSE-OCCUR rule on term: " << tp_term
                             << " with explanation: " << exp << std::endl;
      Node fact = polarity ? MEMBER(reversedTuple, tp_term) : MEMBER(reversedTuple, tp_term).negate();
      sendInfer(fact, exp, "transpose-occur");
      return;
    }

    Node tp_t0_rep      = getRepresentative(tp_term[0]);
    Node reason         = atom[1] == tp_term ? exp : Rewriter::rewrite(AND(exp, EQUAL(atom[1], tp_term)));
    Node fact           = MEMBER(reversedTuple, tp_t0_rep);

    if(!polarity) {
      // tp_term is a nested term and we eagerly compute its subterms' members
      if(d_terms_cache[tp_t0_rep].find(kind::JOIN)
         != d_terms_cache[tp_t0_rep].end()) {
        std::vector<Node> join_terms = d_terms_cache[tp_t0_rep][kind::JOIN];
        for(unsigned int i = 0; i < join_terms.size(); i++) {
          if(d_rel_nodes.find(join_terms[i]) == d_rel_nodes.end()) {
            computeRels(join_terms[i]);
          }
        }
      }
      if(d_terms_cache[tp_t0_rep].find(kind::PRODUCT)
         != d_terms_cache[tp_t0_rep].end()) {
        std::vector<Node> product_terms = d_terms_cache[tp_t0_rep][kind::PRODUCT];
        for(unsigned int i = 0; i < product_terms.size(); i++) {
          if(d_rel_nodes.find(product_terms[i]) == d_rel_nodes.end()) {
            computeRels(product_terms[i]);
          }
        }
      }
      fact = fact.negate();
    }
    sendInfer(fact, reason, "transpose-rule");    
  }


  void TheorySetsRels::inferTC( Node exp, Node tc_rep, std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph,
                                Node start_node, Node cur_node, std::hash_set< Node, NodeHashFunction >& traversed ) {
    Node                                                pair    = constructPair(tc_rep, start_node, cur_node);
    std::map<Node, std::vector<Node> >::iterator        mem_it  = d_membership_db.find(tc_rep);

    if(mem_it != d_membership_db.end()) {
      if(std::find(mem_it->second.begin(), mem_it->second.end(), pair) == mem_it->second.end()) {
        sendLemma( MEMBER(pair, tc_rep), Rewriter::rewrite(exp), "Transitivity" );
      }
    }
    // check if cur_node has been traversed or not
    if(traversed.find(cur_node) != traversed.end()) {
      return;
    }

    traversed.insert(cur_node);
    Node                                                                reason  = exp;
    std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator cur_set = tc_graph.find(cur_node);

    if(cur_set != tc_graph.end()) {
      for(std::hash_set< Node, NodeHashFunction >::iterator set_it = cur_set->second.begin();
          set_it != cur_set->second.end(); set_it++) {
        Node new_pair = constructPair( tc_rep, cur_node, *set_it );
        Assert(!reason.isNull());
        inferTC( AND( findMemExp(tc_rep, new_pair), reason ), tc_rep, tc_graph, start_node, *set_it, traversed );
      }
    }
  }

  void TheorySetsRels::finalizeTCInfer() {
    Trace("rels-debug") << "[sets-rels] Finalizing transitive closure inferences!" << std::endl;
    for(TC_IT tc_it = d_membership_tc_cache.begin(); tc_it != d_membership_tc_cache.end(); tc_it++) {
      inferTC(tc_it->first, tc_it->second);
    }
  }

  void TheorySetsRels::inferTC(Node tc_rep, std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph) {
    Trace("rels-debug") << "[sets-rels] Build TC graph for tc_rep = " << tc_rep << std::endl;
    for(std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator pair_set_it = tc_graph.begin();
        pair_set_it != tc_graph.end(); pair_set_it++) {
      for(std::hash_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();
          set_it != pair_set_it->second.end(); set_it++) {
        std::hash_set<Node, NodeHashFunction>   elements;
        Node                                    pair    = constructPair(tc_rep, pair_set_it->first, *set_it);
        Node                                    exp     = findMemExp(tc_rep, pair);

        if(d_membership_tc_exp_cache.find(tc_rep) != d_membership_tc_exp_cache.end()) {
          exp = AND(d_membership_tc_exp_cache[tc_rep], exp);
        }
        Assert(!exp.isNull());
        elements.insert(pair_set_it->first);
        inferTC( exp, tc_rep, tc_graph, pair_set_it->first, *set_it, elements );
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

    Node                n_rep   = getRepresentative(n);
    Node                n0_rep  = getRepresentative(n[0]);
    std::vector<Node>   tuples  = d_membership_db[n0_rep];
    std::vector<Node>   exps    = d_membership_exp_db[n0_rep];
    Assert(tuples.size() == exps.size());
    for(unsigned int i = 0; i < tuples.size(); i++) {
      Node reason       = exps[i][1] == n0_rep ? exps[i] : AND(exps[i], EQUAL(exps[i][1], n0_rep));
      Node rev_tup      = getRepresentative(RelsUtils::reverseTuple(tuples[i]));
      Node fact         = MEMBER(rev_tup, n_rep);

      if(holds(fact)) {
        Trace("rels-debug") << "[sets-rels] New fact: " << fact << " already holds! Skip..." << std::endl;
      } else {
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
    Node r1             = n[0];
    Node r2             = n[1];
    Node r1_rep         = getRepresentative(r1);
    Node r2_rep         = getRepresentative(r2);
    NodeManager* nm     = NodeManager::currentNM();

    Trace("rels-debug") << "[sets-rels] start composing tuples in relations "
                        << r1 << " and " << r2 << std::endl;

    if(d_membership_db.find(r1_rep) == d_membership_db.end() ||
       d_membership_db.find(r2_rep) == d_membership_db.end())
    return;

    std::vector<Node> new_tups;
    std::vector<Node> new_exps;
    std::vector<Node> r1_elements       = d_membership_db[r1_rep];
    std::vector<Node> r2_elements       = d_membership_db[r2_rep];
    std::vector<Node> r1_exps           = d_membership_exp_db[r1_rep];
    std::vector<Node> r2_exps           = d_membership_exp_db[r2_rep];

    Node new_rel        = n.getKind() == kind::JOIN ? nm->mkNode(kind::JOIN, r1_rep, r2_rep)
                                             : nm->mkNode(kind::PRODUCT, r1_rep, r2_rep);

    Node new_rel_rep    = getRepresentative(new_rel);
    unsigned int t1_len = r1_elements.front().getType().getTupleLength();
    unsigned int t2_len = r2_elements.front().getType().getTupleLength();

    for(unsigned int i = 0; i < r1_elements.size(); i++) {
      for(unsigned int j = 0; j < r2_elements.size(); j++) {
        std::vector<Node>       composed_tuple;
        TypeNode                tn              = n.getType().getSetElementType();
        Node                    r1_rmost        = RelsUtils::nthElementOfTuple(r1_elements[i], t1_len-1);
        Node                    r2_lmost        = RelsUtils::nthElementOfTuple(r2_elements[j], 0);
        composed_tuple.push_back(Node::fromExpr(tn.getDatatype()[0].getConstructor()));

        if((areEqual(r1_rmost, r2_lmost) && n.getKind() == kind::JOIN) ||
            n.getKind() == kind::PRODUCT) {
          bool isProduct = n.getKind() == kind::PRODUCT;
          unsigned int k = 0;
          unsigned int l = 1;

          for(; k < t1_len - 1; ++k) {
            composed_tuple.push_back(RelsUtils::nthElementOfTuple(r1_elements[i], k));
          }
          if(isProduct) {
            composed_tuple.push_back(RelsUtils::nthElementOfTuple(r1_elements[i], k));
            composed_tuple.push_back(RelsUtils::nthElementOfTuple(r2_elements[j], 0));
          }
          for(; l < t2_len; ++l) {
            composed_tuple.push_back(RelsUtils::nthElementOfTuple(r2_elements[j], l));
          }
          Node composed_tuple_rep       = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, composed_tuple));
          Node fact                     = MEMBER(composed_tuple_rep, new_rel_rep);

          if(holds(fact)) {
            Trace("rels-debug") << "[sets-rels] New fact: " << fact << " already holds! Skip..." << std::endl;
          } else {
            std::vector<Node> reasons;
            //Todo: need more explanation
            reasons.push_back(explain(r1_exps[i]));            
            reasons.push_back(explain(r2_exps[j]));
            if(r1_exps[i].getKind() == kind::MEMBER && r1_exps[i][0] != r1_elements[i]) {
              reasons.push_back(explain(EQUAL(r1_elements[i], r1_exps[i][0])));            
            }
            if(r2_exps[j].getKind() == kind::MEMBER && r2_exps[j][0] != r2_elements[j]) {
              reasons.push_back(explain(EQUAL(r2_elements[j], r2_exps[j][0])));            
            }
            if(!isProduct) {              
              if(r1_rmost != r2_lmost) {
                reasons.push_back(explain(EQUAL(r1_rmost, r2_lmost)));
              }
            }
            if(r1 != r1_rep) {
              reasons.push_back(explain(EQUAL(r1, r1_rep)));
            }
            if(r2 != r2_rep) {
              reasons.push_back(explain(EQUAL(r2, r2_rep)));
            }

            Node reason = Rewriter::rewrite(nm->mkNode(kind::AND, reasons));
            if(isProduct) {
              sendInfer( fact, reason, "product-compose" );
            } else {
              sendInfer( fact, reason, "join-compose" );
            }

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
        Assert(d_lemma_cache[i].getKind() == kind::IMPLIES);
        if(holds( d_lemma_cache[i][1] )) {
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
    d_rel_nodes.clear();
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
    d_id_node.clear();
    d_node_id.clear();
  }

  void TheorySetsRels::sendSplit(Node a, Node b, const char * c) {
    Node eq             = a.eqNode( b );
    Node neq            = NOT( eq );
    Node lemma_or       = OR( eq, neq );

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
      Node exp  = d_pending_facts[ fact ];

      if(fact.getKind() == kind::AND) {
        for(size_t j=0; j<fact.getNumChildren(); j++) {
          bool polarity = fact[j].getKind() != kind::NOT;
          Node atom     = polarity ? fact[j] : fact[j][0];
          assertMembership(atom, exp, polarity);
        }
      } else {
        bool polarity   = fact.getKind() != kind::NOT;
        Node atom       = polarity ? fact : fact[0];
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
      Node exp  = d_pending_split_facts[ fact ];

      if(fact.getKind() == kind::AND) {
        for(size_t j=0; j<fact.getNumChildren(); j++) {
          bool polarity = fact[j].getKind() != kind::NOT;
          Node atom     = polarity ? fact[j] : fact[j][0];
          assertMembership(atom, exp, polarity);
        }
      } else {
        Trace("rels-lemma") << "[sets-split-fact] Send " << fact << " from " << exp << std::endl;
        bool polarity   = fact.getKind() != kind::NOT;
        Node atom       = polarity ? fact : fact[0];
        assertMembership(atom, exp, polarity);
      }
      map_it++;
    }
    d_pending_split_facts.clear();
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
    Assert(a.getType() == b.getType());
    Trace("rels-eq") << "[sets-rels]**** checking equality between " << a << " and " << b << std::endl;
    if(a == b) {
      return true;
    } else if( hasTerm( a ) && hasTerm( b ) ){
      return d_eqEngine->areEqual( a, b );
    } else if(a.getType().isTuple()) {
      bool equal = true;
      for(unsigned int i = 0; i < a.getType().getTupleLength(); i++) {
        equal = equal && areEqual(RelsUtils::nthElementOfTuple(a, i), RelsUtils::nthElementOfTuple(b, i));
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
    std::map< Node, std::vector< Node > >::iterator mem_it = map.find(rel_rep);
    if(mem_it == map.end()) {
      std::vector<Node> members;
      members.push_back(member);
      map[rel_rep] = members;
      return true;
    } else {
      std::vector<Node>::iterator mems = mem_it->second.begin();
      while(mems != mem_it->second.end()) {
        if(areEqual(*mems, member)) {
          return false;
        }
        mems++;
      }
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
    Trace("rels-reason") << "[sets-rels] getReason(" << tc_rep << ", " << tc_term << ", " << tc_r_rep << ", " << tc_r << std::endl;
    if(tc_term != tc_rep) {
      Node reason = explain(EQUAL(tc_term, tc_rep));

      if(tc_term[0] != tc_r_rep) {
        return AND(reason, explain(EQUAL(tc_term[0], tc_r_rep)));
      }
    }
    Trace("rels-reason") << "[sets-rels] done getReason(" << tc_rep << ", " << tc_term << ", " << tc_r_rep << ", " << tc_r << std::endl;
    return Node::null();
  }

  // tuple might be a member of tc_rep; or it might be a member of rels or tc_terms such that
  // tc_terms are transitive closure of rels and are modulo equal to tc_rep
  Node TheorySetsRels::findMemExp(Node tc_rep, Node pair) {
    Trace("rels-exp") << "TheorySetsRels::findMemExp ( tc_rep = " << tc_rep << ", pair = " << pair << ")" << std::endl;
    Node                fst             = RelsUtils::nthElementOfTuple(pair, 0);
    Node                snd             = RelsUtils::nthElementOfTuple(pair, 1);
    std::vector<Node>   tc_terms        = d_terms_cache.find(tc_rep)->second[kind::TCLOSURE];

    Assert(tc_terms.size() > 0);
    for(unsigned int i = 0; i < tc_terms.size(); i++) {
      Node tc_term      = tc_terms[i];
      Node tc_r_rep     = getRepresentative(tc_term[0]);

      Trace("rels-exp") << "TheorySetsRels::findMemExp ( r_rep = " << tc_r_rep << ", pair = " << pair << ")" << std::endl;
      std::map< Node, std::vector< Node > >::iterator tc_r_mems = d_membership_db.find(tc_r_rep);
      if(tc_r_mems != d_membership_db.end()) {
        for(unsigned int i = 0; i < tc_r_mems->second.size(); i++) {
          Node fst_mem = RelsUtils::nthElementOfTuple(tc_r_mems->second[i], 0);
          Node snd_mem = RelsUtils::nthElementOfTuple(tc_r_mems->second[i], 1);

          if(areEqual(fst_mem, fst) && areEqual(snd_mem, snd)) {
            Node exp = MEMBER(tc_r_mems->second[i], tc_r_mems->first);

            if(tc_r_rep != tc_term[0]) {
              exp = explain(EQUAL(tc_r_rep, tc_term[0]));
            }
            if(tc_rep != tc_term) {
              exp = AND(exp, explain(EQUAL(tc_rep, tc_term)));
            }
            if(tc_r_mems->second[i] != pair) {
              if(fst_mem != fst) {
                exp = AND(exp, explain(EQUAL(fst_mem, fst)));
              }
              if(snd_mem != snd) {
                exp = AND(exp, explain(EQUAL(snd_mem, snd)));
              }
              exp = AND(exp, EQUAL(tc_r_mems->second[i], pair));
            }
            return Rewriter::rewrite(AND(exp, explain(d_membership_exp_db[tc_r_rep][i])));
          }
        }
      }

      Node                                              tc_term_rep     = getRepresentative(tc_terms[i]);
      std::map< Node, std::vector< Node > >::iterator   tc_t_mems       = d_membership_db.find(tc_term_rep);

      if(tc_t_mems != d_membership_db.end()) {
        for(unsigned int j = 0; j < tc_t_mems->second.size(); j++) {
          Node fst_mem = RelsUtils::nthElementOfTuple(tc_t_mems->second[j], 0);
          Node snd_mem = RelsUtils::nthElementOfTuple(tc_t_mems->second[j], 1);

          if(areEqual(fst_mem, fst) && areEqual(snd_mem, snd)) {
            Node exp = MEMBER(tc_t_mems->second[j], tc_t_mems->first);
            if(tc_rep != tc_terms[i]) {
              exp = AND(exp, explain(EQUAL(tc_rep, tc_terms[i])));
            }
            if(tc_term_rep != tc_terms[i]) {
              exp = AND(exp, explain(EQUAL(tc_term_rep, tc_terms[i])));
            }
            if(tc_t_mems->second[j] != pair) {
              if(fst_mem != fst) {
                exp = AND(exp, explain(EQUAL(fst_mem, fst)));
              }
              if(snd_mem != snd) {
                exp = AND(exp, explain(EQUAL(snd_mem, snd)));
              }
              exp = AND(exp, EQUAL(tc_t_mems->second[j], pair));
            }
            return Rewriter::rewrite(AND(exp, explain(d_membership_exp_db[tc_term_rep][j])));
          }
        }
      }
    }
    return Node::null();
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
    Trace("rels-share") << " [sets-rels] making shared term " << n << std::endl;
    if(d_shared_terms.find(n) == d_shared_terms.end()) {
      Node skolem = NodeManager::currentNM()->mkSkolem( "sde", n.getType() );
      sendLemma(MEMBER(skolem, SINGLETON(n)), d_trueNode, "share-term");
      d_shared_terms.insert(n);
    }
  }

  bool TheorySetsRels::holds(Node node) {
    Trace("rels-check") << " [sets-rels] Check if node = " << node << " already holds " << std::endl;
    bool polarity       = node.getKind() != kind::NOT;
    Node atom           = polarity ? node : node[0];
    Node polarity_atom  = polarity ? d_trueNode : d_falseNode;

    if(d_eqEngine->hasTerm(atom)) {
      Trace("rels-check") << " [sets-rels] node = " << node << " is in the EE " << std::endl;
      return areEqual(atom, polarity_atom);
    } else {
      Node atom_mod = NodeManager::currentNM()->mkNode(atom.getKind(),
                                                       getRepresentative(atom[0]),
                                                       getRepresentative(atom[1]));
      if(d_eqEngine->hasTerm(atom_mod)) {
        return areEqual(atom_mod, polarity_atom);
      }
    }
    return false;
  }

  void TheorySetsRels::computeTupleReps( Node n ) {
    if( d_tuple_reps.find( n ) == d_tuple_reps.end() ){
      for( unsigned i = 0; i < n.getType().getTupleLength(); i++ ){
        d_tuple_reps[n].push_back( getRepresentative( RelsUtils::nthElementOfTuple(n, i) ) );
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
        Node element = RelsUtils::nthElementOfTuple(n[0], i);
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
    d_eqEngine(eq),
    d_sets_theory(d_set),
    d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
    d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
    d_pending_merge(c),
    d_infer(c),
    d_infer_exp(c),
    d_lemma(u),
    d_shared_terms(u),
    d_tc_saver(u),
    d_conflict(conflict)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TCLOSURE);
  }

  TheorySetsRels::~TheorySetsRels() {}

  std::vector<Node> TupleTrie::findTerms( std::vector< Node >& reps, int argIndex ) {
    std::vector<Node>                           nodes;
    std::map< Node, TupleTrie >::iterator       it;

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
    Trace("rels-exp") << "[sets-rels] TheorySetsRels::explain(" << literal << ")"<< std::endl;
    std::vector<TNode>  assumptions;
    bool                polarity        = literal.getKind() != kind::NOT;
    TNode               atom            = polarity ? literal : literal[0];

    if(atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
      d_eqEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
    } else if(atom.getKind() == kind::MEMBER) {
      if( !d_eqEngine->hasTerm(atom)) {
        d_eqEngine->addTerm(atom);
      }
      d_eqEngine->explainPredicate(atom, polarity, assumptions);
    } else {
      Trace("rels-exp") << "unhandled: " << literal << "; (" << atom << ", "
                    << polarity << "); kind" << atom.getKind() << std::endl;
      Unhandled();
    }
    Trace("rels-exp") << "[sets-rels] ****** done with TheorySetsRels::explain(" << literal << ")"<< std::endl;
    return mkAnd(assumptions);
  }

  TheorySetsRels::EqcInfo::EqcInfo( context::Context* c ) :
  d_mem(c), d_not_mem(c), d_in(c), d_out(c), d_mem_exp(c),
  d_tp(c), d_pt(c), d_join(c), d_tc(c), d_id_in(c), d_id_out(c) {}

  void TheorySetsRels::eqNotifyNewClass( Node n ) {
    Trace("rels-std") << "[sets-rels] eqNotifyNewClass:" << " t = " << n << std::endl;
    if(isRel(n) && (n.getKind() == kind::TRANSPOSE || 
                    n.getKind() == kind::PRODUCT ||
                    n.getKind() == kind::JOIN ||
                    n.getKind() == kind::TCLOSURE)) {
      getOrMakeEqcInfo( n, true );
    }
  }

  // Create a integer id for tuple element
  int TheorySetsRels::getOrMakeElementRepId(EqcInfo* ei, Node e_rep) {
    Trace("rels-std") << "[sets-rels] getOrMakeElementRepId:" << " e_rep = " << e_rep << std::endl;
    std::map<Node, int>::iterator       nid_it  = d_node_id.find(e_rep);

    if( nid_it == d_node_id.end() ) {
      Trace("rels-std") << "[sets-rels] getOrMakeElementRepId:" << " *** 0"<< std::endl;
      if(d_eqEngine->hasTerm(e_rep)) {
        // it is possible that e's rep changes at this moment, thus we need to know the eqc of e's previous rep
        eq::EqClassIterator rep_eqc_i = eq::EqClassIterator( e_rep, d_eqEngine );
        Trace("rels-std") << "[sets-rels] getOrMakeElementRepId:" << " *** 1"<< std::endl;
        while(!rep_eqc_i.isFinished()) {
          std::map<Node, int>::iterator id_it = d_node_id.find(*rep_eqc_i);

          if( id_it != d_node_id.end() ) {
            d_id_node[id_it->second]    = e_rep;
            d_node_id[e_rep]            = id_it->second;
            return id_it->second;
          }
          rep_eqc_i++;
        }
      }
      d_id_node[ei->counter]    = e_rep;
      d_node_id[e_rep]          = ei->counter;
      ei->counter++;
      return ei->counter-1;
    }
    Trace("rels-std") << "[sets-rels] finish getOrMakeElementRepId:" << " e_rep = " << e_rep << std::endl;
    return nid_it->second;
  }

  bool TheorySetsRels::insertIntoIdList(IdList& idList, int mem) {
    IdList::const_iterator      idListIt = idList.begin();
    while(idListIt != idList.end()) {
      if(*idListIt == mem) {
        return false;
      }
      idListIt++;
    }
    idList.push_back(mem);
    return true;
  }

  void TheorySetsRels::addTCMemAndSendInfer(EqcInfo* tc_ei, Node membership, Node exp, bool fromRel) {
    Trace("rels-std") << "[sets-rels] addTCMemAndSendInfer:" << " membership = " << membership << " from a relation? " << fromRel<< std::endl;
    IdList*     in_lst;
    IdList*     out_lst;
    Node        fst             = RelsUtils::nthElementOfTuple(membership[0], 0);
    Node        snd             = RelsUtils::nthElementOfTuple(membership[0], 1);
    Node        fst_rep         = getRepresentative(fst);
    Node        snd_rep         = getRepresentative(snd);
    Node        mem_rep         = RelsUtils::constructPair(tc_ei->d_tc, fst_rep, snd_rep);
    int         fst_rep_id      = getOrMakeElementRepId(tc_ei, fst_rep);
    int         snd_rep_id      = getOrMakeElementRepId(tc_ei, snd_rep);

    IdListMap::iterator         tc_in_mem_it    = tc_ei->d_id_in.find(snd_rep_id);

    if(tc_in_mem_it == tc_ei->d_id_in.end()) {
      in_lst = new(d_sets_theory.getSatContext()->getCMM()) IdList( true, d_sets_theory.getSatContext(), false,
                                                                      context::ContextMemoryAllocator<TNode>(d_sets_theory.getSatContext()->getCMM()) );
      tc_ei->d_id_in.insertDataFromContextMemory(snd_rep_id, in_lst);
      Trace("rels-std") << "Create in cache for " << snd_rep << std::endl;
    } else {
      in_lst = (*tc_in_mem_it).second;
    }
    // If fst_rep is inserted into in_lst successfully,
    // save rep pair's exp and send out TC inference lemmas.
    // Otherwise, mem's rep is already in the TC and return.
    if(insertIntoIdList(*in_lst, fst_rep_id)) {
      Node reason       = exp == Node::null() ? explain(membership) : exp;
      if(!fromRel && tc_ei->d_tc.get() != membership[1]) {
        reason  = AND(reason, explain(EQUAL(tc_ei->d_tc.get(), membership[1])));
      }
      if(fst != fst_rep) {
        reason  = AND(reason, explain(EQUAL(fst, fst_rep)));
      }
      if(snd != snd_rep) {
        reason  = AND(reason, explain(EQUAL(snd, snd_rep)));
      }
      tc_ei->d_mem_exp[mem_rep] = reason;
      Trace("rels-std") << "Added member " << mem_rep << " for " << tc_ei->d_tc.get()<< " with reason = " << reason << std::endl;
      tc_ei->d_mem.insert(mem_rep);
      Trace("rels-std") << "Added in membership arrow for " << snd_rep << " from: " << fst_rep << std::endl;
    } else {
      // Nothing inserted into the eqc
      return;
    }

    IdListMap::iterator tc_out_mem_it = tc_ei->d_id_out.find(fst_rep_id);
    if(tc_out_mem_it == tc_ei->d_id_out.end()) {
      out_lst = new(d_sets_theory.getSatContext()->getCMM()) IdList( true, d_sets_theory.getSatContext(), false,
                                                                            context::ContextMemoryAllocator<TNode>(d_sets_theory.getSatContext()->getCMM()) );
      tc_ei->d_id_out.insertDataFromContextMemory(fst_rep_id, out_lst);
      Trace("rels-std") << "Create out arrow cache for " << snd_rep << std::endl;
    } else {
      out_lst = (*tc_out_mem_it).second;
    }
    insertIntoIdList(*out_lst, snd_rep_id);
    Trace("rels-std") << "Add out membership arrow for " << fst_rep << " to : " << snd_rep << std::endl;
    sendTCInference(tc_ei, mem_rep, fst_rep, snd_rep, fst_rep_id, snd_rep_id);
  }

  Node TheorySetsRels::explainTCMem(EqcInfo* ei, Node pair, Node fst, Node snd) {
    if(ei->d_mem_exp.find(pair) != ei->d_mem_exp.end()) {
      return (*ei->d_mem_exp.find(pair)).second;
    }
    NodeMap::iterator   mem_exp_it      = ei->d_mem_exp.begin();
    while(mem_exp_it != ei->d_mem_exp.end()) {
      Node      tuple   = (*mem_exp_it).first;
      Node      fst_e   = RelsUtils::nthElementOfTuple(tuple, 0);
      Node      snd_e   = RelsUtils::nthElementOfTuple(tuple, 1);
      if(areEqual(fst, fst_e) && areEqual(snd, snd_e)) {
        return AND(explain(EQUAL(snd, snd_e)), AND(explain(EQUAL(fst, fst_e)), (*mem_exp_it).second));
      }
      ++mem_exp_it;
    }
    return Node::null();
  }

  void TheorySetsRels::sendTCInference(EqcInfo* tc_ei, Node mem_rep, Node fst_rep, Node snd_rep, int id1, int id2) {
    Trace("rels-std") << "Start making TC inference after adding a member " << mem_rep << " to " << tc_ei->d_tc.get() << std::endl;
    Node exp            = explainTCMem(tc_ei, mem_rep, fst_rep, snd_rep);
    Node tc_lemma       = NodeManager::currentNM()->mkNode(kind::IMPLIES, exp, MEMBER(mem_rep, tc_ei->d_tc.get()));
    d_pending_merge.push_back(tc_lemma);
    d_lemma.insert(tc_lemma);

    std::hash_set<int>       in_reachable;
    std::hash_set<int>       out_reachable;
    collectInReachableNodes(tc_ei, id1, in_reachable);
    collectOutReachableNodes(tc_ei, id2, out_reachable);
    Trace("rels-std") << "Start making TC inference after adding a member " << mem_rep << " to " << tc_ei->d_tc.get() <<  " ***** 2" << std::endl;
    std::hash_set<int>::iterator        in_reachable_it = in_reachable.begin();
    while(in_reachable_it != in_reachable.end()) {
      Node    in_node         = d_id_node[*in_reachable_it];
      Node    in_pair         = RelsUtils::constructPair(tc_ei->d_tc.get(), in_node, fst_rep);
      Node    new_pair        = RelsUtils::constructPair(tc_ei->d_tc.get(), in_node, snd_rep);
      Node    reason          = AND(explainTCMem(tc_ei, in_pair, in_node, fst_rep), exp);
      Trace("rels-std") << "***$$$$$$$$$$ Adding exp for " << new_pair << " with reason " << reason << std::endl;
      tc_ei->d_mem_exp[new_pair] = reason;
      tc_ei->d_mem.insert(new_pair);
      Node tc_lemma = NodeManager::currentNM()->mkNode(kind::IMPLIES, reason, MEMBER(new_pair, tc_ei->d_tc.get()));
      d_pending_merge.push_back(tc_lemma);
      d_lemma.insert(tc_lemma);
      in_reachable_it++;
    }
    Trace("rels-std") << "Start making TC inference after adding a member " << mem_rep << " to " << tc_ei->d_tc.get() <<  " ***** 3" << std::endl;
    std::hash_set<int>::iterator        out_reachable_it = out_reachable.begin();
    while(out_reachable_it != out_reachable.end()) {
      Node    out_node        = d_id_node[*out_reachable_it];
      Node    out_pair        = RelsUtils::constructPair(tc_ei->d_tc.get(), snd_rep, out_node);
      Node    reason          = explainTCMem(tc_ei, out_pair, snd_rep, out_node);
      Assert(reason != Node::null());

      std::hash_set<int>::iterator        in_reachable_it = in_reachable.begin();
      while(in_reachable_it != in_reachable.end()) {
        Node    in_node         = d_id_node[*in_reachable_it];
        Node    in_pair         = RelsUtils::constructPair(tc_ei->d_tc.get(), in_node, snd_rep);
        Node    new_pair        = RelsUtils::constructPair(tc_ei->d_tc.get(), in_node, out_node);
        Node    in_pair_exp     = explainTCMem(tc_ei, in_pair, in_node, snd_rep);

        Assert(in_pair_exp != Node::null());
        reason                = AND(reason, in_pair_exp);

        Trace("rels-std") << "Start making TC inference after adding a member " << mem_rep << " to " << tc_ei->d_tc.get() <<  " ***** 3 9" << std::endl;
        tc_ei->d_mem_exp[new_pair] = reason;
        tc_ei->d_mem.insert(new_pair);
        Node tc_lemma = NodeManager::currentNM()->mkNode(kind::IMPLIES, reason, MEMBER(new_pair, tc_ei->d_tc.get()));
        d_pending_merge.push_back(tc_lemma);
        d_lemma.insert(tc_lemma);
        in_reachable_it++;
      }
      out_reachable_it++;
    }
    Trace("rels-std") << "Start making TC inference after adding a member " << mem_rep << " to " << tc_ei->d_tc.get() <<  " ***** 4" << std::endl;
  }

  void TheorySetsRels::collectInReachableNodes(EqcInfo* tc_ei, int start_id, std::hash_set<int>& in_reachable, bool firstRound) {
    Trace("rels-std") << "Start collecting in-reachable nodes for node with id " << start_id <<  " ***** 0" << std::endl;
    if(in_reachable.find(start_id) != in_reachable.end()) {
      return;
    }
    if(!firstRound) {
      in_reachable.insert(start_id);
    }
    IdListMap::const_iterator id_list_map_it = tc_ei->d_id_in.find(start_id);

    if(id_list_map_it != tc_ei->d_id_in.end()) {
      IdList::const_iterator id_list_it = (*id_list_map_it).second->begin();
      while(id_list_it != (*id_list_map_it).second->end()) {
        collectInReachableNodes(tc_ei, *id_list_it, in_reachable, false);
        id_list_it++;
      }
    }
  }

  void TheorySetsRels::collectOutReachableNodes(EqcInfo* tc_ei, int start_id, std::hash_set<int>& out_reachable, bool firstRound) {
    Trace("rels-std") << "Start collecting out-reachable nodes for node with id " << start_id <<  " ***** 0" << std::endl;
    if(out_reachable.find(start_id) != out_reachable.end()) {
      return;
    }
    if(!firstRound) {
      out_reachable.insert(start_id);
    }
    IdListMap::const_iterator id_list_map_it = tc_ei->d_id_out.find(start_id);

    if(id_list_map_it != tc_ei->d_id_out.end()) {
      IdList::const_iterator id_list_it = (*id_list_map_it).second->begin();
      while(id_list_it != (*id_list_map_it).second->end()) {
        collectOutReachableNodes(tc_ei, *id_list_it, out_reachable, false);
        id_list_it++;
      }
    }
  }

  // Merge t2 into t1, t1 will be the rep of the new eqc
  void TheorySetsRels::eqNotifyPostMerge( Node t1, Node t2 ) {
    Trace("rels-std") << "[sets-rels] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;

    // Merge membership constraint with "true" or "false" eqc
    // Todo: t1 might not be "true" or "false" rep
    if((t1 == d_trueNode || t1 == d_falseNode) &&
        t2.getKind() == kind::MEMBER &&
        t2[0].getType().isTuple()) {

      Assert(t1 == d_trueNode || t1 == d_falseNode);
      bool      polarity        = t1 == d_trueNode;
      Node      t2_1rep         = getRepresentative(t2[1]);
      EqcInfo*  ei              = getOrMakeEqcInfo( t2_1rep );

      if(ei == NULL) {
        ei = getOrMakeEqcInfo( t2_1rep, true );
      }
      if(polarity) {
        ei->d_mem.insert(t2[0]);
        ei->d_mem_exp[t2[0]] = explain(t2);
      } else {
        ei->d_not_mem.insert(t2[0]);
      }
      // Process a membership constraint that a tuple is a member of transpose of rel
      if(!ei->d_tp.get().isNull()) {
        Node exp = polarity ? explain(t2) : explain(t2.negate());
        if(ei->d_tp.get() != t2[1]) {
          exp = AND( explain(EQUAL( ei->d_tp.get(), t2[1]) ), exp );
        }
        sendInferTranspose( polarity, t2[0], ei->d_tp.get(), exp, true );
      }
      // Process a membership constraint that a tuple is a member of product of rel
      if(!ei->d_pt.get().isNull()) {
        Node exp = polarity ? explain(t2) : explain(t2.negate());
        if(ei->d_pt.get() != t2[1]) {
          exp = AND( explain(EQUAL( ei->d_pt.get(), t2[1]) ), exp );
        }
        sendInferProduct(polarity, t2[0], ei->d_pt.get(), exp);
      }
      // Process a membership constraint that a tuple is a member of transitive closure of rel
      if(polarity) {
        if(!ei->d_tc.get().isNull()) {
          addTCMemAndSendInfer(ei, t2, Node::null());
        // when we see (a, b) in R and TC(R) has not been seen, we create a EQC for TC(R) to save (a, b)
        } else {
          std::vector<TypeNode> tup_types = t2[1].getType().getSetElementType().getTupleTypes();

          if( tup_types.size() == 2 && tup_types[0] == tup_types[1] ) {
            Node        tc_n    = NodeManager::currentNM()->mkNode(kind::TCLOSURE, t2[1]);
            EqcInfo*    tc_ei   = getOrMakeEqcInfo( tc_n );
            if( tc_ei != NULL ) {
              addTCMemAndSendInfer(tc_ei, t2, Node::null(), true);
            }
          }
        }
      }

    // Merge two relation eqcs
    } else if(t1.getType().isSet() &&
              t2.getType().isSet() &&
              t1.getType().getSetElementType().isTuple()) {
      mergeTransposeEqcs(t1, t2);
      mergeProductEqcs(t1, t2);
      mergeTCEqcs(t1, t2);
    }

    Trace("rels-std") << "[sets-rels] done with eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  }

  void TheorySetsRels::mergeTCEqcs(Node t1, Node t2) {
    Trace("rels-std") << "[sets-rels] Merge TC eqcs t1 = " << t1 << " and t2 = " << t2 << std::endl;
    EqcInfo* t1_ei = getOrMakeEqcInfo(t1);
    EqcInfo* t2_ei = getOrMakeEqcInfo(t2);

    if(t1_ei != NULL && t2_ei != NULL) {
      NodeSet::const_iterator     non_mem_it  = t2_ei->d_not_mem.begin();
      while(non_mem_it != t2_ei->d_not_mem.end()) {
        t1_ei->d_not_mem.insert(*non_mem_it);
        non_mem_it++;
      }
      if(!t1_ei->d_tc.get().isNull()) {
        NodeSet::const_iterator     mem_it  = t2_ei->d_mem.begin();
        while(mem_it != t2_ei->d_mem.end()) {
          addTCMemAndSendInfer(t1_ei, MEMBER(*mem_it, t2_ei->d_tc.get()), (*t2_ei->d_mem_exp.find(*mem_it)).second);
          mem_it++;
        }
      } else if(!t2_ei->d_tc.get().isNull()) {
        t1_ei->d_tc.set(t2_ei->d_tc);
        NodeSet::const_iterator     t1_mem_it  = t1_ei->d_mem.begin();
        while(t1_mem_it != t1_ei->d_mem.end()) {
          addTCMemAndSendInfer(t1_ei, MEMBER(*t1_mem_it, t1_ei->d_tc.get()), (*t1_ei->d_mem_exp.find(*t1_mem_it)).second);
          t1_mem_it++;
        }
        NodeSet::const_iterator     t2_mem_it  = t2_ei->d_mem.begin();
        while(t2_mem_it != t2_ei->d_mem.end()) {
          addTCMemAndSendInfer(t1_ei, MEMBER(*t2_mem_it, t2_ei->d_tc.get()), (*t2_ei->d_mem_exp.find(*t2_mem_it)).second);
          t2_mem_it++;
        }
      }
    }
    Trace("rels-std") << "[sets-rels] Done with merging TC eqcs t1 = " << t1 << " and t2 = " << t2 << std::endl;
  }




  void TheorySetsRels::mergeProductEqcs(Node t1, Node t2) {
    Trace("rels-std") << "[sets-rels] Merge PRODUCT eqcs t1 = " << t1 << " and t2 = " << t2 << std::endl;
    EqcInfo* t1_ei = getOrMakeEqcInfo(t1);
    EqcInfo* t2_ei = getOrMakeEqcInfo(t2);
    if(t1_ei != NULL && t2_ei != NULL) {
      // PT(t1) = PT(t2) -> t1 = t2;
      if(!t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull()) {
        sendInferProduct( true, t1_ei->d_pt.get(), t2_ei->d_pt.get(), explain(EQUAL(t1, t2)) );
      }
      // Apply Product rule on (non)members of t2 and t1->pt
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
    Trace("rels-std") << "[sets-rels] Merge TRANSPOSE eqcs t1 = " << t1 << " and t2 = " << t2 << std::endl;
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
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(RelsUtils::reverseTuple(t1), t2[0]) );
      } else {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(RelsUtils::reverseTuple(t1), t2[0]).negate() );
      }
    } else {
      Node n2;
      if(polarity) {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(t1, t2) );
        n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(RelsUtils::reverseTuple(t1), t2[0]) );
      } else {
        n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(t1, t2).negate() );
        n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(RelsUtils::reverseTuple(t1), t2[0]).negate() );
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
      //PRODUCT(x) = PRODUCT(y) => x = y;
      Assert(t1.getKind() == kind::PRODUCT);
      Node n = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, EQUAL(t1[0], t2[0]) );
      Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying product rule: "
                        << n << std::endl;
      d_pending_merge.push_back(n);
      d_lemma.insert(n);
      return;
    }

    std::vector<Node>   r1_element;
    std::vector<Node>   r2_element;
    Node                r1      = t2[0];
    Node                r2      = t2[1];
    NodeManager         *nm     = NodeManager::currentNM();
    Datatype            dt      = r1.getType().getSetElementType().getDatatype();
    unsigned int        i       = 0;
    unsigned int        s1_len  = r1.getType().getSetElementType().getTupleLength();
    unsigned int        tup_len = t2.getType().getSetElementType().getTupleLength();

    r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < s1_len; ++i) {
      r1_element.push_back(RelsUtils::nthElementOfTuple(t1, i));
    }

    dt = r2.getType().getSetElementType().getDatatype();
    r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < tup_len; ++i) {
      r2_element.push_back(RelsUtils::nthElementOfTuple(t1, i));
    }

    Node n1;
    Node n2;
    Node tuple_1 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r1_element));
    Node tuple_2 = getRepresentative(nm->mkNode(kind::APPLY_CONSTRUCTOR, r2_element));

    if(polarity) {
      n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_1, r1) );
      n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_2, r2) );
    } else {
      n1 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_1, r1).negate() );
      n2 = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, MEMBER(tuple_2, r2).negate() );
    }
    Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying product-split rule: "
                      << n1 << std::endl;
    d_pending_merge.push_back(n1);
    d_lemma.insert(n1);
    Trace("rels-std") << "[sets-rels-lemma] Generate a lemma by applying product-split rule: "
                      << n2 << std::endl;
    d_pending_merge.push_back(n2);
    d_lemma.insert(n2);

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
        } else if(n.getKind() == kind::TCLOSURE) {
          ei->d_tc = n;
        } else if(n.getKind() == kind::JOIN) {
          ei->d_join = n;
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














