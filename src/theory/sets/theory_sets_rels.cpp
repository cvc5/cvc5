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
#include "theory/sets/theory_sets_private.h"
#include "theory/sets/theory_sets.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace sets {

typedef std::map< Node, std::vector< Node > >::iterator                                         MEM_IT;
typedef std::map< kind::Kind_t, std::vector< Node > >::iterator                                 KIND_TERM_IT;
typedef std::map< Node, std::hash_set< Node, NodeHashFunction > >::iterator                     TC_GRAPH_IT;
typedef std::map< Node, std::map< kind::Kind_t, std::vector< Node > > >::iterator               TERM_IT;
typedef std::map< Node, std::map< Node, std::hash_set< Node, NodeHashFunction > > >::iterator   TC_IT;

int TheorySetsRels::EqcInfo::counter        = 0;

  void TheorySetsRels::check(Theory::Effort level) {
    Trace("rels") << "\n[sets-rels] ******************************* Start the relational solver, effort = " << level << " *******************************\n" << std::endl;
    if(Theory::fullEffort(level)) {
      collectRelsInfo();
      check();
      doPendingLemmas();
      Assert( d_lemmas_out.empty() );
      Assert( d_pending_facts.empty() );
    } else {
      doPendingMerge();
    }
    Trace("rels") << "\n[sets-rels] ******************************* Done with the relational solver *******************************\n" << std::endl;
  }

  void TheorySetsRels::check() {
    MEM_IT m_it = d_rReps_memberReps_cache.begin();

    while(m_it != d_rReps_memberReps_cache.end()) {
      Node rel_rep = m_it->first;

      for(unsigned int i = 0; i < m_it->second.size(); i++) {
        Node    mem     = d_rReps_memberReps_cache[rel_rep][i];
        Node    exp     = d_rReps_memberReps_exp_cache[rel_rep][i];
        std::map<kind::Kind_t, std::vector<Node> >    kind_terms      = d_terms_cache[rel_rep];

        if( kind_terms.find(kind::TRANSPOSE) != kind_terms.end() ) {
          std::vector<Node> tp_terms = kind_terms[kind::TRANSPOSE];
          // exp is a membership term and tp_terms contains all
          // transposed terms that are equal to the right hand side of exp
          if( tp_terms.size() > 0 ) {
            applyTransposeRule( tp_terms );
            applyTransposeRule( tp_terms[0], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::JOIN) != kind_terms.end() ) {
          std::vector<Node> join_terms = kind_terms[kind::JOIN];
          // exp is a membership term and join_terms contains all
          // terms involving "join" operator that are in the same
          // equivalence class with the right hand side of exp
          for( unsigned int j = 0; j < join_terms.size(); j++ ) {
            applyJoinRule( join_terms[j], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::PRODUCT) != kind_terms.end() ) {
          std::vector<Node> product_terms = kind_terms[kind::PRODUCT];
          for( unsigned int j = 0; j < product_terms.size(); j++ ) {
            applyProductRule( product_terms[j], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::TCLOSURE) != kind_terms.end() ) {
          std::vector<Node> tc_terms = kind_terms[kind::TCLOSURE];
          for( unsigned int j = 0; j < tc_terms.size(); j++ ) {
            applyTCRule( mem, tc_terms[j], rel_rep, exp );
          }
        }
      }
      m_it++;
    }

    TERM_IT t_it = d_terms_cache.begin();
    while( t_it != d_terms_cache.end() ) {
      if( d_rReps_memberReps_cache.find(t_it->first) == d_rReps_memberReps_cache.end() ) {
        Trace("rels-debug") << "[sets-rels] A term does not have membership constraints: " << t_it->first << std::endl;
        KIND_TERM_IT k_t_it = t_it->second.begin();

        while( k_t_it != t_it->second.end() ) {
          if( k_t_it->first == kind::JOIN || k_t_it->first == kind::PRODUCT ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while(term_it != k_t_it->second.end()) {
              computeMembersForBinOpRel( *term_it );
              term_it++;
            }
          } else if( k_t_it->first == kind::TRANSPOSE ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              computeMembersForUnaryOpRel( *term_it );
              term_it++;
            }
          } else if ( k_t_it->first == kind::TCLOSURE ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              buildTCGraphForRel( *term_it );
              term_it++;
            }

          }
          k_t_it++;
        }
      }
      t_it++;
    }
    doTCInference();
  }

  /*
   * Populate relational terms data structure
   */

  void TheorySetsRels::collectRelsInfo() {
    Trace("rels") << "[sets-rels] Start collecting relational terms..." << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );
    while( !eqcs_i.isFinished() ){
      Node                      eqc_rep  = (*eqcs_i);
      eq::EqClassIterator       eqc_i   = eq::EqClassIterator( eqc_rep, d_eqEngine );

      Trace("rels-ee") << "[sets-rels-ee] Eqc term representative: " << eqc_rep << std::endl;

      while( !eqc_i.isFinished() ){
        Node eqc_node = (*eqc_i);

        Trace("rels-ee") << "  term : " << eqc_node << std::endl;

        if( getRepresentative(eqc_rep) == getRepresentative(d_trueNode) ||
            getRepresentative(eqc_rep) == getRepresentative(d_falseNode) ) {
          // collect membership info
          if( eqc_node.getKind() == kind::MEMBER && eqc_node[1].getType().getSetElementType().isTuple() ) {
            Node tup_rep = getRepresentative( eqc_node[0] );
            Node rel_rep = getRepresentative( eqc_node[1] );

            if( eqc_node[0].isVar() ){
              reduceTupleVar( eqc_node );
            }

            bool is_true_eq    = areEqual( eqc_rep, d_trueNode );
            Node reason        = is_true_eq ? eqc_node : eqc_node.negate();

            if( is_true_eq ) {
              if( safelyAddToMap(d_rReps_memberReps_cache, rel_rep, tup_rep) ) {
                addToMap(d_rReps_memberReps_exp_cache, rel_rep, reason);
                computeTupleReps(tup_rep);
                d_membership_trie[rel_rep].addTerm(tup_rep, d_tuple_reps[tup_rep]);
              }
            } else {
              if( safelyAddToMap(d_rReps_nonMemberReps_cache, rel_rep, tup_rep) ) {
                addToMap(d_rReps_nonMemberReps_exp_cache, rel_rep, reason);
              }
            }
          }
        // collect relational terms info
        } else if( eqc_rep.getType().isSet() && eqc_rep.getType().getSetElementType().isTuple() ) {
          if( eqc_node.getKind() == kind::TRANSPOSE || eqc_node.getKind() == kind::JOIN ||
              eqc_node.getKind() == kind::PRODUCT || eqc_node.getKind() == kind::TCLOSURE ) {
            std::vector<Node> terms;
            std::map< kind::Kind_t, std::vector<Node> >  rel_terms;
            TERM_IT terms_it = d_terms_cache.find(eqc_rep);

            if( terms_it == d_terms_cache.end() ) {
              terms.push_back(eqc_node);
              rel_terms[eqc_node.getKind()]      = terms;
              d_terms_cache[eqc_rep]             = rel_terms;
            } else {
              KIND_TERM_IT kind_term_it = terms_it->second.find(eqc_node.getKind());

              if( kind_term_it == terms_it->second.end() ) {
                terms.push_back(eqc_node);
                d_terms_cache[eqc_rep][eqc_node.getKind()] = terms;
              } else {
                kind_term_it->second.push_back(eqc_node);
              }
            }
          }
        // need to add all tuple elements as shared terms
        } else if( eqc_node.getType().isTuple() && !eqc_node.isConst() && !eqc_node.isVar() ) {
          for( unsigned int i = 0; i < eqc_node.getType().getTupleLength(); i++ ) {
            Node element = RelsUtils::nthElementOfTuple( eqc_node, i );

            if( !element.isConst() ) {
              makeSharedTerm( element );
            }
          }
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    Trace("rels-debug") << "[Theory::Rels] Done with collecting relational terms!" << std::endl;
  }

  /*
   * Construct transitive closure graph for tc_rep based on the members of tc_r_rep
   */

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
   */
  void TheorySetsRels::applyTCRule( Node mem_rep, Node tc_rel, Node tc_rel_rep, Node exp ) {
    Trace("rels-debug") << "[Theory::Rels] *********** Applying TCLOSURE rule on a tc term = " << tc_rel
                            << ", its representative = " << tc_rel_rep
                            << " with member rep = " << mem_rep << " and explanation = " << exp << std::endl;
    MEM_IT mem_it = d_rReps_memberReps_cache.find( tc_rel[0] );

    if( mem_it != d_rReps_memberReps_cache.end() && d_rel_nodes.find( tc_rel ) == d_rel_nodes.end()
        && d_rRep_tcGraph.find( getRepresentative( tc_rel[0] ) ) ==  d_rRep_tcGraph.end() ) {
      buildTCGraphForRel( tc_rel );
      d_rel_nodes.insert( tc_rel );
    }

    // mem_rep is a member of tc_rel[0] or mem_rep can be infered by TC_Graph of tc_rel[0], thus skip
    if( isTCReachable( mem_rep, tc_rel) ) {
      Trace("rels-debug") << "[Theory::Rels] mem_rep is a member of tc_rel[0] = " << tc_rel[0]
                              << " or can be infered by TC_Graph of tc_rel[0]! " << std::endl;
      return;
    }
    // add mem_rep to d_tcrRep_tcGraph
    TC_IT tc_it = d_tcr_tcGraph.find( tc_rel );
    Node mem_rep_fst = getRepresentative( RelsUtils::nthElementOfTuple( mem_rep, 0 ) );
    Node mem_rep_snd = getRepresentative( RelsUtils::nthElementOfTuple( mem_rep, 1 ) );
    Node mem_rep_tup = RelsUtils::constructPair( tc_rel, mem_rep_fst, mem_rep_snd );

    if( tc_it != d_tcr_tcGraph.end() ) {
      std::map< Node, std::map< Node, Node > >::iterator tc_exp_it = d_tcr_tcGraph_exps.find( tc_rel );

      TC_GRAPH_IT tc_graph_it = (tc_it->second).find( mem_rep_fst );
      Assert( tc_exp_it != d_tcr_tcGraph_exps.end() );
      std::map< Node, Node >::iterator exp_map_it = (tc_exp_it->second).find( mem_rep_tup );

      if( exp_map_it == (tc_exp_it->second).end() ) {
        (tc_exp_it->second)[mem_rep_tup] = exp;
      }

      if( tc_graph_it != (tc_it->second).end() ) {
        (tc_graph_it->second).insert( mem_rep_snd );
      } else {
        std::hash_set< Node, NodeHashFunction > sets;
        sets.insert( mem_rep_snd );
        (tc_it->second)[mem_rep_fst] = sets;
      }
    } else {
      std::map< Node, Node > exp_map;
      std::hash_set< Node, NodeHashFunction > sets;
      std::map< Node, std::hash_set<Node, NodeHashFunction> > element_map;
      sets.insert( mem_rep_snd );
      element_map[mem_rep_fst] = sets;
      d_tcr_tcGraph[tc_rel] = element_map;
      exp_map[mem_rep_tup] = exp;
      d_tcr_tcGraph_exps[tc_rel] = exp_map;
    }

    Node fst_element = RelsUtils::nthElementOfTuple( exp[0], 0 );
    Node snd_element = RelsUtils::nthElementOfTuple( exp[0], 1 );
    Node sk_1     = NodeManager::currentNM()->mkSkolem("stc", fst_element.getType());
    Node sk_2     = NodeManager::currentNM()->mkSkolem("stc", snd_element.getType());
    Node mem_of_r = NodeManager::currentNM()->mkNode(kind::MEMBER, exp[0], tc_rel[0]);
    Node sk_eq    = NodeManager::currentNM()->mkNode(kind::EQUAL, sk_1, sk_2);
    Node reason   = exp;

    if( tc_rel != exp[1] ) {
      reason = NodeManager::currentNM()->mkNode(kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, tc_rel, exp[1]));
    }

    Node conclusion = NodeManager::currentNM()->mkNode(kind::OR, mem_of_r,
                                                     (NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::constructPair(tc_rel, fst_element, sk_1), tc_rel[0]),
                                                     (NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::constructPair(tc_rel, sk_2, snd_element), tc_rel[0]),
                                                     (NodeManager::currentNM()->mkNode(kind::OR, sk_eq, NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::constructPair(tc_rel, sk_1, sk_2), tc_rel))))))));

    Node tc_lemma = NodeManager::currentNM()->mkNode(kind::IMPLIES, reason, conclusion );
    std::vector< Node > require_phase;
    require_phase.push_back(Rewriter::rewrite(mem_of_r));
    require_phase.push_back(Rewriter::rewrite(sk_eq));
    d_tc_lemmas_last[tc_lemma] = require_phase;
  }

  bool TheorySetsRels::isTCReachable( Node mem_rep, Node tc_rel ) {
    MEM_IT mem_it = d_rReps_memberReps_cache.find( getRepresentative( tc_rel[0] ) );

    if( mem_it != d_rReps_memberReps_cache.end() && std::find( (mem_it->second).begin(), (mem_it->second).end(), mem_rep) != (mem_it->second).end() ) {
      return true;
    }

    TC_IT tc_it = d_rRep_tcGraph.find( getRepresentative(tc_rel[0]) );
    if( tc_it != d_rRep_tcGraph.end() ) {
      bool isReachable = false;
      std::hash_set<Node, NodeHashFunction> seen;
      isTCReachable( getRepresentative( RelsUtils::nthElementOfTuple(mem_rep, 0) ),
                     getRepresentative( RelsUtils::nthElementOfTuple(mem_rep, 1) ), seen, tc_it->second, isReachable );
      return isReachable;
    }
    return false;
  }

  void TheorySetsRels::isTCReachable( Node start, Node dest, std::hash_set<Node, NodeHashFunction>& hasSeen,
                                    std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph, bool& isReachable ) {
    if(hasSeen.find(start) == hasSeen.end()) {
      hasSeen.insert(start);
    }

    TC_GRAPH_IT pair_set_it = tc_graph.find(start);

    if(pair_set_it != tc_graph.end()) {
      if(pair_set_it->second.find(dest) != pair_set_it->second.end()) {
        isReachable = true;
        return;
      } else {
        std::hash_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();

        while( set_it != pair_set_it->second.end() ) {
          // need to check if *set_it has been looked already
          if( hasSeen.find(*set_it) == hasSeen.end() ) {
            isTCReachable( *set_it, dest, hasSeen, tc_graph, isReachable );
          }
          set_it++;
        }
      }
    }
  }

  void TheorySetsRels::buildTCGraphForRel( Node tc_rel ) {
    std::map< Node, Node > rel_tc_graph_exps;
    std::map< Node, std::hash_set<Node, NodeHashFunction> > rel_tc_graph;

    Node rel_rep = getRepresentative( tc_rel[0] );
    Node tc_rel_rep = getRepresentative( tc_rel );
    std::vector< Node > members = d_rReps_memberReps_cache[rel_rep];
    std::vector< Node > exps = d_rReps_memberReps_exp_cache[rel_rep];

    for( unsigned int i = 0; i < members.size(); i++ ) {
      Node fst_element_rep = getRepresentative( RelsUtils::nthElementOfTuple( members[i], 0 ));
      Node snd_element_rep = getRepresentative( RelsUtils::nthElementOfTuple( members[i], 1 ));
      Node tuple_rep = RelsUtils::constructPair( rel_rep, fst_element_rep, snd_element_rep );
      std::map< Node, std::hash_set<Node, NodeHashFunction> >::iterator rel_tc_graph_it = rel_tc_graph.find( fst_element_rep );

      if( rel_tc_graph_it == rel_tc_graph.end() ) {
        std::hash_set< Node, NodeHashFunction > snd_elements;
        snd_elements.insert( snd_element_rep );
        rel_tc_graph[fst_element_rep] = snd_elements;
        rel_tc_graph_exps[tuple_rep] = exps[i];
      } else if( (rel_tc_graph_it->second).find( snd_element_rep ) ==  (rel_tc_graph_it->second).end() ) {
        (rel_tc_graph_it->second).insert( snd_element_rep );
        rel_tc_graph_exps[tuple_rep] = exps[i];
      }
    }

    if( members.size() > 0 ) {
      d_rRep_tcGraph[rel_rep] = rel_tc_graph;
      d_tcr_tcGraph_exps[tc_rel] = rel_tc_graph_exps;
      d_tcr_tcGraph[tc_rel] = rel_tc_graph;
    }
  }

  void TheorySetsRels::doTCInference( std::map< Node, std::hash_set<Node, NodeHashFunction> > rel_tc_graph, std::map< Node, Node > rel_tc_graph_exps, Node tc_rel ) {
    Trace("rels-debug") << "[Theory::Rels] ****** doTCInference !" << std::endl;
    for( TC_GRAPH_IT tc_graph_it = rel_tc_graph.begin(); tc_graph_it != rel_tc_graph.end(); tc_graph_it++ ) {
      for( std::hash_set< Node, NodeHashFunction >::iterator snd_elements_it = tc_graph_it->second.begin();
           snd_elements_it != tc_graph_it->second.end(); snd_elements_it++ ) {
        std::vector< Node > reasons;
        std::hash_set<Node, NodeHashFunction> seen;
        Node tuple = RelsUtils::constructPair( tc_rel, getRepresentative( tc_graph_it->first ), getRepresentative( *snd_elements_it) );
        Assert( rel_tc_graph_exps.find( tuple ) != rel_tc_graph_exps.end() );
        Node exp   = rel_tc_graph_exps.find( tuple )->second;

        reasons.push_back( exp );
        seen.insert( tc_graph_it->first );
        doTCInference( tc_rel, reasons, rel_tc_graph, rel_tc_graph_exps, tc_graph_it->first, *snd_elements_it, seen);
      }
    }
    Trace("rels-debug") << "[Theory::Rels] ****** Done with doTCInference !" << std::endl;
  }

  void TheorySetsRels::doTCInference(Node tc_rel, std::vector< Node > reasons, std::map< Node, std::hash_set< Node, NodeHashFunction > >& tc_graph,
                                       std::map< Node, Node >& rel_tc_graph_exps, Node start_node_rep, Node cur_node_rep, std::hash_set< Node, NodeHashFunction >& seen ) {
    Node tc_mem = RelsUtils::constructPair( tc_rel, RelsUtils::nthElementOfTuple((reasons.front())[0], 0), RelsUtils::nthElementOfTuple((reasons.back())[0], 1) );
    std::vector< Node > all_reasons( reasons );

    for( unsigned int i = 0 ; i < reasons.size()-1; i++ ) {
      Node fst_element_end = RelsUtils::nthElementOfTuple( reasons[i][0], 1 );
      Node snd_element_begin = RelsUtils::nthElementOfTuple( reasons[i+1][0], 0 );
      if( fst_element_end != snd_element_begin ) {
        all_reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, fst_element_end, snd_element_begin) );
      }
      if( tc_rel != reasons[i][1] && tc_rel[0] != reasons[i][1] ) {
        all_reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, tc_rel[0], reasons[i][1]) );
      }
    }
    if( tc_rel != reasons.back()[1] && tc_rel[0] != reasons.back()[1] ) {
      all_reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, tc_rel[0], reasons.back()[1]) );
    }
    if( all_reasons.size() > 1) {
      sendInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, tc_mem, tc_rel), NodeManager::currentNM()->mkNode(kind::AND, all_reasons), "TCLOSURE-Forward");
    } else {
      sendInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, tc_mem, tc_rel), all_reasons.front(), "TCLOSURE-Forward");
    }

    // check if cur_node has been traversed or not
    if( seen.find( cur_node_rep ) != seen.end() ) {
      return;
    }
    seen.insert( cur_node_rep );
    TC_GRAPH_IT  cur_set = tc_graph.find( cur_node_rep );
    if( cur_set != tc_graph.end() ) {
      for( std::hash_set< Node, NodeHashFunction >::iterator set_it = cur_set->second.begin();
           set_it != cur_set->second.end(); set_it++ ) {
        Node new_pair = constructPair( tc_rel, cur_node_rep, *set_it );
        std::vector< Node > new_reasons( reasons );
        new_reasons.push_back( rel_tc_graph_exps.find( new_pair )->second );
        doTCInference( tc_rel, new_reasons, tc_graph, rel_tc_graph_exps, start_node_rep, *set_it, seen );
      }
    }
  }

 /*  product-split rule:  (a, b) IS_IN (X PRODUCT Y)
  *                     ----------------------------------
  *                       a IS_IN X  && b IS_IN Y
  *
  *  product-compose rule: (a, b) IS_IN X    (c, d) IS_IN Y
  *                        ---------------------------------
  *                        (a, b, c, d) IS_IN (X PRODUCT Y)
  */


  void TheorySetsRels::applyProductRule( Node pt_rel, Node pt_rel_rep, Node exp ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** Applying PRODUCT rule on producted term = " << pt_rel
                            << ", its representative = " << pt_rel_rep
                            << " with explanation = " << exp << std::endl;

    if(d_rel_nodes.find( pt_rel ) == d_rel_nodes.end()) {
      Trace("rels-debug") <<  "\n[Theory::Rels] Apply PRODUCT-COMPOSE rule on term: " << pt_rel
                          << " with explanation: " << exp << std::endl;

      computeMembersForBinOpRel( pt_rel );
      d_rel_nodes.insert( pt_rel );
    }

    Node mem = exp[0];
    std::vector<Node>   r1_element;
    std::vector<Node>   r2_element;
    Datatype     dt      = pt_rel[0].getType().getSetElementType().getDatatype();
    unsigned int s1_len  = pt_rel[0].getType().getSetElementType().getTupleLength();
    unsigned int tup_len = pt_rel.getType().getSetElementType().getTupleLength();

    r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));

    unsigned int i = 0;
    for(; i < s1_len; ++i) {
      r1_element.push_back(RelsUtils::nthElementOfTuple(mem, i));
    }
    dt = pt_rel[1].getType().getSetElementType().getDatatype();
    r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < tup_len; ++i) {
      r2_element.push_back(RelsUtils::nthElementOfTuple(mem, i));
    }
    Node reason   = exp;
    Node mem1     = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r1_element);
    Node mem2     = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r2_element);
    Node fact_1   = NodeManager::currentNM()->mkNode(kind::MEMBER, mem1, pt_rel[0]);
    Node fact_2   = NodeManager::currentNM()->mkNode(kind::MEMBER, mem2, pt_rel[1]);

    if( pt_rel != exp[1] ) {
      reason = NodeManager::currentNM()->mkNode(kind::AND, exp, explain(NodeManager::currentNM()->mkNode(kind::EQUAL, pt_rel, exp[1])));
    }
    sendInfer( fact_1, reason, "product-split" );
    sendInfer( fact_2, reason, "product-split" );
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

  void TheorySetsRels::applyJoinRule( Node join_rel, Node join_rel_rep, Node exp ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** Applying JOIN rule on joined term = " << join_rel
                            << ", its representative = " << join_rel_rep
                            << " with explanation = " << exp << std::endl;
    if(d_rel_nodes.find( join_rel ) == d_rel_nodes.end()) {
      Trace("rels-debug") <<  "\n[Theory::Rels] Apply JOIN-COMPOSE rule on term: " << join_rel
                          << " with explanation: " << exp << std::endl;

      computeMembersForBinOpRel( join_rel );
      d_rel_nodes.insert( join_rel );
    }

    Node mem = exp[0];
    std::vector<Node> r1_element;
    std::vector<Node> r2_element;
    Node r1_rep = getRepresentative(join_rel[0]);
    Node r2_rep = getRepresentative(join_rel[1]);
    TypeNode     shared_type    = r2_rep.getType().getSetElementType().getTupleTypes()[0];
    Node         shared_x       = NodeManager::currentNM()->mkSkolem("srj_", shared_type);
    Datatype     dt             = join_rel[0].getType().getSetElementType().getDatatype();
    unsigned int s1_len         = join_rel[0].getType().getSetElementType().getTupleLength();
    unsigned int tup_len        = join_rel.getType().getSetElementType().getTupleLength();

    unsigned int i = 0;
    r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for(; i < s1_len-1; ++i) {
      r1_element.push_back(RelsUtils::nthElementOfTuple(mem, i));
    }
    r1_element.push_back(shared_x);
    dt = join_rel[1].getType().getSetElementType().getDatatype();
    r2_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    r2_element.push_back(shared_x);
    for(; i < tup_len; ++i) {
      r2_element.push_back(RelsUtils::nthElementOfTuple(mem, i));
    }
    Node mem1 = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r1_element);
    Node mem2 = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, r2_element);

    computeTupleReps(mem1);
    computeTupleReps(mem2);

    std::vector<Node> elements = d_membership_trie[r1_rep].findTerms(d_tuple_reps[mem1]);
    for(unsigned int j = 0; j < elements.size(); j++) {
      std::vector<Node> new_tup;
      new_tup.push_back(elements[j]);
      new_tup.insert(new_tup.end(), d_tuple_reps[mem2].begin()+1, d_tuple_reps[mem2].end());
      if(d_membership_trie[r2_rep].existsTerm(new_tup) != Node::null()) {
        return;
      }
    }
    Node reason = exp;
    if( join_rel != exp[1] ) {
      reason = NodeManager::currentNM()->mkNode(kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, join_rel, exp[1]));
    }
    Node fact = NodeManager::currentNM()->mkNode(kind::MEMBER, mem1, join_rel[0]);
    sendInfer( fact, reason, "JOIN-Split" );
    fact = NodeManager::currentNM()->mkNode(kind::MEMBER, mem2, join_rel[1]);
    sendInfer( fact, reason, "JOIN-Split" );
    makeSharedTerm( shared_x );
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
   * Not implemented yet!
   * transpose-equal rule:   [NOT]  (TRANSPOSE X) = (TRANSPOSE Y)
   *                         -----------------------------------------------
   *                         [NOT]  (X = Y)
   */
  void TheorySetsRels::applyTransposeRule( std::vector<Node> tp_terms ) {
    if( tp_terms.size() < 1) {
      return;
    }
    for( unsigned int i = 1; i < tp_terms.size(); i++ ) {
      Trace("rels-debug") << "\n[Theory::Rels] *********** Applying TRANSPOSE-Equal rule on transposed term = " << tp_terms[0] << " and " << tp_terms[i] << std::endl;
      sendInfer(NodeManager::currentNM()->mkNode(kind::EQUAL, tp_terms[0][0], tp_terms[i][0]), NodeManager::currentNM()->mkNode(kind::EQUAL, tp_terms[0], tp_terms[i]), "TRANSPOSE-Equal");
    }
  }

  void TheorySetsRels::applyTransposeRule( Node tp_rel, Node tp_rel_rep, Node exp ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** Applying TRANSPOSE rule on transposed term = " << tp_rel
                        << ", its representative = " << tp_rel_rep
                        << " with explanation = " << exp << std::endl;

    if(d_rel_nodes.find( tp_rel ) == d_rel_nodes.end()) {
      Trace("rels-debug") <<  "\n[Theory::Rels] Apply TRANSPOSE-Compose rule on term: " << tp_rel
                          << " with explanation: " << exp << std::endl;

      computeMembersForUnaryOpRel( tp_rel );
      d_rel_nodes.insert( tp_rel );
    }

    Node reason = exp;
    Node reversed_mem = RelsUtils::reverseTuple( exp[0] );

    if( tp_rel != exp[1] ) {
      reason = NodeManager::currentNM()->mkNode(kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, tp_rel, exp[1]));
    }
    sendInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, reversed_mem, tp_rel[0]), reason, "TRANSPOSE-Reverse" );
  }

  void TheorySetsRels::doTCInference() {
    Trace("rels-debug") << "[Theory::Rels] ****** Finalizing transitive closure inferences!" << std::endl;
    TC_IT tc_graph_it = d_tcr_tcGraph.begin();
    while( tc_graph_it != d_tcr_tcGraph.end() ) {
      Assert ( d_tcr_tcGraph_exps.find(tc_graph_it->first) != d_tcr_tcGraph_exps.end() );
      doTCInference( tc_graph_it->second, d_tcr_tcGraph_exps.find(tc_graph_it->first)->second, tc_graph_it->first );
      tc_graph_it++;
    }
    Trace("rels-debug") << "[Theory::Rels] ****** Done with finalizing transitive closure inferences!" << std::endl;
  }


  // Bottom-up fashion to compute relations with more than 1 arity
  void TheorySetsRels::computeMembersForBinOpRel(Node rel) {
    Trace("rels-debug") << "\n[Theory::Rels] computeMembersForBinOpRel for relation  " << rel << std::endl;

    switch(rel[0].getKind()) {
      case kind::TRANSPOSE:
      case kind::TCLOSURE: {
        computeMembersForUnaryOpRel(rel[0]);
        break;
      }
      case kind::JOIN:
      case kind::PRODUCT: {
        computeMembersForBinOpRel(rel[0]);
        break;
      }
      default:
        break;
    }
    switch(rel[1].getKind()) {
      case kind::TRANSPOSE: {
        computeMembersForUnaryOpRel(rel[1]);
        break;
      }
      case kind::JOIN:
      case kind::PRODUCT: {
        computeMembersForBinOpRel(rel[1]);
        break;
      }
      default:
        break;
    }
    if(d_rReps_memberReps_cache.find(getRepresentative(rel[0])) == d_rReps_memberReps_cache.end() ||
       d_rReps_memberReps_cache.find(getRepresentative(rel[1])) == d_rReps_memberReps_cache.end()) {
      return;
    }
    composeMembersForRels(rel);
  }

  // Bottom-up fashion to compute unary relation
  void TheorySetsRels::computeMembersForUnaryOpRel(Node rel) {
    Trace("rels-debug") << "\n[Theory::Rels] computeMembersForUnaryOpRel for relation  " << rel << std::endl;

    switch(rel[0].getKind()) {
      case kind::TRANSPOSE:
      case kind::TCLOSURE:
        computeMembersForUnaryOpRel(rel[0]);
        break;
      case kind::JOIN:
      case kind::PRODUCT:
        computeMembersForBinOpRel(rel[0]);
        break;
      default:
        break;
    }

    Node rel0_rep  = getRepresentative(rel[0]);
    if(d_rReps_memberReps_cache.find( rel0_rep ) == d_rReps_memberReps_cache.end())
      return;

    std::vector<Node>   members = d_rReps_memberReps_cache[rel0_rep];
    std::vector<Node>   exps    = d_rReps_memberReps_exp_cache[rel0_rep];

    Assert( members.size() == exps.size() );

    for(unsigned int i = 0; i < members.size(); i++) {
      Node reason = exps[i];
      if( rel.getKind() == kind::TRANSPOSE) {
        if( rel[0] != exps[i][1] ) {
          reason = NodeManager::currentNM()->mkNode(kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, rel[0], exps[i][1]));
        }
        sendInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::reverseTuple(exps[i][0]), rel), reason, "TRANSPOSE-reverse");
      }
    }
  }

  /*
   * Explicitly compose the join or product relations of r1 and r2
   * e.g. If (a, b) in X and (b, c) in Y, (a, c) in (X JOIN Y)
   *
   */
  void TheorySetsRels::composeMembersForRels( Node rel ) {
    Trace("rels-debug") << "[Theory::Rels] Start composing members for relation = " << rel << std::endl;
    Node r1 = rel[0];
    Node r2 = rel[1];
    Node r1_rep = getRepresentative( r1 );
    Node r2_rep = getRepresentative( r2 );

    if(d_rReps_memberReps_cache.find( r1_rep ) == d_rReps_memberReps_cache.end() ||
       d_rReps_memberReps_cache.find( r2_rep ) == d_rReps_memberReps_cache.end() ) {
      return;
    }

    std::vector<Node> r1_rep_exps = d_rReps_memberReps_exp_cache[r1_rep];
    std::vector<Node> r2_rep_exps = d_rReps_memberReps_exp_cache[r2_rep];
    unsigned int r1_tuple_len = r1.getType().getSetElementType().getTupleLength();
    unsigned int r2_tuple_len = r2.getType().getSetElementType().getTupleLength();

    for( unsigned int i = 0; i < r1_rep_exps.size(); i++ ) {
      for( unsigned int j = 0; j < r2_rep_exps.size(); j++ ) {
        std::vector<Node> tuple_elements;
        TypeNode tn = rel.getType().getSetElementType();
        Node r1_rmost = RelsUtils::nthElementOfTuple( r1_rep_exps[i][0], r1_tuple_len-1 );
        Node r2_lmost = RelsUtils::nthElementOfTuple( r2_rep_exps[j][0], 0 );
        tuple_elements.push_back( Node::fromExpr(tn.getDatatype()[0].getConstructor()) );

        if( (areEqual(r1_rmost, r2_lmost) && rel.getKind() == kind::JOIN) ||
            rel.getKind() == kind::PRODUCT ) {
          bool isProduct = rel.getKind() == kind::PRODUCT;
          unsigned int k = 0;
          unsigned int l = 1;

          for( ; k < r1_tuple_len - 1; ++k ) {
            tuple_elements.push_back( RelsUtils::nthElementOfTuple( r1_rep_exps[i][0], k ) );
          }
          if(isProduct) {
            tuple_elements.push_back( RelsUtils::nthElementOfTuple( r1_rep_exps[i][0], k ) );
            tuple_elements.push_back( RelsUtils::nthElementOfTuple( r2_rep_exps[j][0], 0 ) );
          }
          for( ; l < r2_tuple_len; ++l ) {
            tuple_elements.push_back( RelsUtils::nthElementOfTuple( r2_rep_exps[j][0], l ) );
          }

          Node composed_tuple = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, tuple_elements);
          Node fact = NodeManager::currentNM()->mkNode(kind::MEMBER, composed_tuple, rel);
          std::vector<Node> reasons;
          reasons.push_back( r1_rep_exps[i] );
          reasons.push_back( r2_rep_exps[j] );

          if( r1 != r1_rep_exps[i][1] ) {
            reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, r1, r1_rep_exps[i][1]) );
          }
          if( r2 != r2_rep_exps[j][1] ) {
            reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, r2, r2_rep_exps[j][1]) );
          }
          if( isProduct ) {
            sendInfer( fact, NodeManager::currentNM()->mkNode(kind::AND, reasons), "PRODUCT-Compose" );
          } else {
            if( r1_rmost != r2_lmost ) {
              reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, r1_rmost, r2_lmost) );
            }
            sendInfer( fact, NodeManager::currentNM()->mkNode(kind::AND, reasons), "JOIN-Compose" );
          }
        }
      }
    }

  }

  void TheorySetsRels::doPendingLemmas() {
    Trace("rels-debug") << "[Theory::Rels] **************** Start doPendingLemmas !" << std::endl;
    if( !(*d_conflict) ){
      if ( (!d_lemmas_out.empty() || !d_pending_facts.empty()) ) {
        for( unsigned i=0; i < d_lemmas_out.size(); i++ ){
          Assert(d_lemmas_out[i].getKind() == kind::IMPLIES);
          if(holds( d_lemmas_out[i][1] )) {
            Trace("rels-lemma-skip") << "[sets-rels-lemma-skip] Skip an already held lemma: "
                                     << d_lemmas_out[i]<< std::endl;
            continue;
          }
          d_sets_theory.d_out->lemma( d_lemmas_out[i] );
          Trace("rels-lemma") << "[sets-rels-lemma] Send out a lemma : "
                              << d_lemmas_out[i] << std::endl;
        }
        for( std::map<Node, Node>::iterator pending_it = d_pending_facts.begin();
             pending_it != d_pending_facts.end(); pending_it++ ) {
          if( holds( pending_it->first ) ) {
            Trace("rels-lemma-skip") << "[sets-rels-fact-lemma-skip] Skip an already held fact,: "
                                     << pending_it->first << std::endl;
            continue;
          }
          Node lemma = NodeManager::currentNM()->mkNode(kind::IMPLIES, pending_it->second, pending_it->first);
          if( d_lemmas_produced.find( lemma ) == d_lemmas_produced.end() ) {
            d_sets_theory.d_out->lemma(NodeManager::currentNM()->mkNode(kind::IMPLIES, pending_it->second, pending_it->first));
            Trace("rels-lemma") << "[sets-rels-fact-lemma] Send out a fact as lemma : "
                                << pending_it->first << " with reason " << pending_it->second << std::endl;
            d_lemmas_produced.insert( lemma );
          }
        }
      }
    }
    doTCLemmas();
    Trace("rels-debug") << "[Theory::Rels] **************** Done with doPendingLemmas !" << std::endl;
    d_tuple_reps.clear();
//    d_id_node.clear();
//    d_node_id.clear();
    d_tuple_reps.clear();
    d_rReps_memberReps_exp_cache.clear();
    d_terms_cache.clear();
    d_lemmas_out.clear();
    d_membership_trie.clear();
    d_rel_nodes.clear();
    d_pending_facts.clear();
    d_rReps_memberReps_cache.clear();
    d_rRep_tcGraph.clear();
    d_tcr_tcGraph_exps.clear();
    d_tcr_tcGraph.clear();
    d_tc_lemmas_last.clear();
  }
  bool TheorySetsRels::isRelationKind( Kind k ) {
    return k == kind::TRANSPOSE || k == kind::PRODUCT || k == kind::JOIN || k == kind::TCLOSURE;
  }
  void TheorySetsRels::doTCLemmas() {
    Trace("rels-debug") << "[Theory::Rels] **************** Start doTCLemmas !" << std::endl;
    std::map< Node, std::vector< Node > >::iterator tc_lemma_it = d_tc_lemmas_last.begin();
    while( tc_lemma_it != d_tc_lemmas_last.end() ) {
      if( !holds( tc_lemma_it->first[1] ) ) {
        if( d_lemmas_produced.find( tc_lemma_it->first ) == d_lemmas_produced.end() ) {
          d_sets_theory.d_out->lemma( tc_lemma_it->first );
          d_lemmas_produced.insert( tc_lemma_it->first );

          for( unsigned int i = 0; i < (tc_lemma_it->second).size(); i++ ) {
            if( (tc_lemma_it->second)[i] == d_falseNode ) {
              d_sets_theory.d_out->requirePhase((tc_lemma_it->second)[i], true);
            }
          }
          Trace("rels-lemma") << "[Theory::Rels] **** Send out a TC lemma = " << tc_lemma_it->first << " by " << "TCLOSURE-Forward"<< std::endl;
        }
      }
      ++tc_lemma_it;
    }
    Trace("rels-debug") << "[Theory::Rels] **************** Done with doTCLemmas !" << std::endl;
  }

  void TheorySetsRels::sendLemma(Node conc, Node ant, const char * c) {
    if( !holds( conc ) ) {
      Node lemma = NodeManager::currentNM()->mkNode(kind::IMPLIES, ant, conc);
      if( d_lemmas_produced.find( lemma ) == d_lemmas_produced.end() ) {
        d_lemmas_out.push_back( lemma );
        d_lemmas_produced.insert( lemma );
        Trace("rels-send-lemma") << "[Theory::Rels] **** Generate a lemma conclusion = " << conc << " with reason = " << ant << " by " << c << std::endl;
      }
    }
  }

  void TheorySetsRels::sendInfer( Node fact, Node exp, const char * c ) {
    if( !holds( fact ) ) {
      Trace("rels-send-lemma") << "[Theory::Rels] **** Generate an infered fact "
                               << fact << " with reason " << exp << " by "<< c << std::endl;
      d_pending_facts[fact] = exp;
    } else {
      Trace("rels-send-lemma-debug") << "[Theory::Rels] **** Generate an infered fact "
                                     << fact << " with reason " << exp << " by "<< c
                                     << ", but it holds already, thus skip it!" << std::endl;
    }
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

  /*
   * Make sure duplicate members are not added in map
   */
  bool TheorySetsRels::safelyAddToMap(std::map< Node, std::vector<Node> >& map, Node rel_rep, Node member) {
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

  void TheorySetsRels::addSharedTerm( TNode n ) {
    Trace("rels-debug") << "[sets-rels] Add a shared term:  " << n << std::endl;
    d_sets_theory.addSharedTerm(n);
    d_eqEngine->addTriggerTerm(n, THEORY_SETS);
  }

  void TheorySetsRels::makeSharedTerm( Node n ) {
    Trace("rels-share") << " [sets-rels] making shared term " << n << std::endl;
    if(d_shared_terms.find(n) == d_shared_terms.end()) {
      Node skolem = NodeManager::currentNM()->mkSkolem( "sts", NodeManager::currentNM()->mkSetType( n.getType() ) );
      sendLemma(skolem.eqNode(NodeManager::currentNM()->mkNode(kind::SINGLETON,n)), d_trueNode, "share-term");
      d_shared_terms.insert(n);
    }
  }

  bool TheorySetsRels::holds(Node node) {
    bool polarity       = node.getKind() != kind::NOT;
    Node atom           = polarity ? node : node[0];
    return d_sets_theory.isEntailed( atom, polarity );
  }

  /*
   * For each tuple n, we store a mapping between n and a list of its elements representatives
   * in d_tuple_reps. This would later be used for applying JOIN operator.
   */
  void TheorySetsRels::computeTupleReps( Node n ) {
    if( d_tuple_reps.find( n ) == d_tuple_reps.end() ){
      for( unsigned i = 0; i < n.getType().getTupleLength(); i++ ){
        d_tuple_reps[n].push_back( getRepresentative( RelsUtils::nthElementOfTuple(n, i) ) );
      }
    }
  }

  inline Node TheorySetsRels::constructPair(Node tc_rep, Node a, Node b) {
    Datatype dt = tc_rep.getType().getSetElementType().getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, Node::fromExpr(dt[0].getConstructor()), a, b);
  }

  /*
   * Node n[0] is a tuple variable, reduce n[0] to a concrete representation,
   * which is (e1, ..., en) where e1, ... ,en are concrete elements of tuple n[0].
   */
  void TheorySetsRels::reduceTupleVar(Node n) {
    if(d_symbolic_tuples.find(n) == d_symbolic_tuples.end()) {
      Trace("rels-debug") << "[Theory::Rels] Reduce tuple var: " << n[0] << " to a concrete one " << " node = " << n << std::endl;
      std::vector<Node> tuple_elements;
      tuple_elements.push_back(Node::fromExpr((n[0].getType().getDatatype())[0].getConstructor()));
      for(unsigned int i = 0; i < n[0].getType().getTupleLength(); i++) {
        Node element = RelsUtils::nthElementOfTuple(n[0], i);
        makeSharedTerm(element);
        tuple_elements.push_back(element);
      }
      Node tuple_reduct = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, tuple_elements);
      tuple_reduct = NodeManager::currentNM()->mkNode(kind::MEMBER,tuple_reduct, n[1]);
      Node tuple_reduction_lemma = NodeManager::currentNM()->mkNode(kind::EQUAL, n, tuple_reduct);
      sendLemma(tuple_reduction_lemma, d_trueNode, "tuple-reduction");
      d_symbolic_tuples.insert(n);
    }
  }

  TheorySetsRels::TheorySetsRels( context::Context* c,
                                  context::UserContext* u,
                                  eq::EqualityEngine* eq,
                                  context::CDO<bool>* conflict,
                                  TheorySets& d_set ):
    d_vec_size(c),
    d_eqEngine(eq),
    d_conflict(conflict),
    d_sets_theory(d_set),
    d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
    d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
    d_pending_merge(c),
    d_lemmas_produced(u),
    d_shared_terms(u)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TCLOSURE);
  }

  TheorySetsRels::~TheorySetsRels() {
    for(std::map< Node, EqcInfo* >::iterator i = d_eqc_info.begin(), iend = d_eqc_info.end();
        i != iend; ++i){
      EqcInfo* current = (*i).second;
      Assert(current != NULL);
      delete current;
    }
  }

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

  Node TheorySetsRels::explain( Node literal ){
    //use lazy explanations
    return literal;
  }

  TheorySetsRels::EqcInfo::EqcInfo( context::Context* c ) :
  d_mem(c), d_mem_exp(c), d_in(c), d_out(c),
  d_tp(c), d_pt(c), d_join(c), d_tc(c) {}

  // Create an integer id for tuple element
  int TheorySetsRels::getOrMakeElementRepId(EqcInfo* ei, Node e_rep) {
    Trace("rels-std") << "[sets-rels] getOrMakeElementRepId:" << " e_rep = " << e_rep << std::endl;
    std::map< Node, int >::iterator nid_it  = d_node_id.find(e_rep);

    if( nid_it == d_node_id.end() ) {
      if( d_eqEngine->hasTerm(e_rep) ) {
        // it is possible that e's rep changes at this moment, thus we need to know the previous rep id of eqc of e
        eq::EqClassIterator rep_eqc_i = eq::EqClassIterator( e_rep, d_eqEngine );
        while( !rep_eqc_i.isFinished() ) {
          std::map< Node, int >::iterator id_it = d_node_id.find(*rep_eqc_i);

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

  void TheorySetsRels::addTCMemAndSendInfer( EqcInfo* tc_ei, Node membership, Node exp, bool fromRel ) {
    Trace("rels-std") << "[sets-rels] addTCMemAndSendInfer:" << " membership = " << membership << " from a relation? " << fromRel<< std::endl;

    Node     fst     = RelsUtils::nthElementOfTuple(membership[0], 0);
    Node     snd     = RelsUtils::nthElementOfTuple(membership[0], 1);
    Node     fst_rep = getRepresentative(fst);
    Node     snd_rep = getRepresentative(snd);
    Node     mem_rep = RelsUtils::constructPair(membership[1], fst_rep, snd_rep);

    if(tc_ei->d_mem.find(mem_rep) != tc_ei->d_mem.end()) {
      return;
    }

    int fst_rep_id = getOrMakeElementRepId( tc_ei, fst_rep );
    int snd_rep_id = getOrMakeElementRepId( tc_ei, snd_rep );

    std::hash_set<int>       in_reachable;
    std::hash_set<int>       out_reachable;
    collectReachableNodes(tc_ei->d_id_inIds, fst_rep_id, in_reachable);
    collectReachableNodes(tc_ei->d_id_outIds, snd_rep_id, out_reachable);

    // If fst_rep is inserted into in_lst successfully,
    // save rep pair's exp and send out TC inference lemmas.
    // Otherwise, mem's rep is already in the TC and return.
    if( addId(tc_ei->d_id_inIds, snd_rep_id, fst_rep_id) ) {
      Node reason       = exp == Node::null() ? explain(membership) : exp;
      if(!fromRel && tc_ei->d_tc.get() != membership[1]) {
        reason  = NodeManager::currentNM()->mkNode(kind::AND,reason, explain(NodeManager::currentNM()->mkNode(kind::EQUAL,tc_ei->d_tc.get(), membership[1])));
      }
      if(fst != fst_rep) {
        reason  = NodeManager::currentNM()->mkNode(kind::AND,reason, explain(NodeManager::currentNM()->mkNode(kind::EQUAL,fst, fst_rep)));
      }
      if(snd != snd_rep) {
        reason  = NodeManager::currentNM()->mkNode(kind::AND,reason, explain(NodeManager::currentNM()->mkNode(kind::EQUAL,snd, snd_rep)));
      }
      tc_ei->d_mem_exp[mem_rep] = reason;
      Trace("rels-std") << "Added member " << mem_rep << " for " << tc_ei->d_tc.get()<< " with reason = " << reason << std::endl;
      tc_ei->d_mem.insert(mem_rep);
      Trace("rels-std") << "Added in membership arrow for " << snd_rep << " from: " << fst_rep << std::endl;
    } else {
      // Nothing inserted into the eqc
      return;
    }
    Trace("rels-std") << "Add out membership arrow for " << fst_rep << " to : " << snd_rep << std::endl;
    addId(tc_ei->d_id_inIds, fst_rep_id, snd_rep_id);
    sendTCInference(tc_ei, in_reachable, out_reachable, mem_rep, fst_rep, snd_rep, fst_rep_id, snd_rep_id);
  }

  Node TheorySetsRels::explainTCMem(EqcInfo* ei, Node pair, Node fst, Node snd) {
    Trace("rels-tc") << "explainTCMem ############ pair = " << pair << std::endl;
    if(ei->d_mem_exp.find(pair) != ei->d_mem_exp.end()) {
      return (*ei->d_mem_exp.find(pair)).second;
    }
    NodeMap::iterator   mem_exp_it      = ei->d_mem_exp.begin();

    while(mem_exp_it != ei->d_mem_exp.end()) {
      Node      tuple   = (*mem_exp_it).first;
      Node      fst_e   = RelsUtils::nthElementOfTuple(tuple, 0);
      Node      snd_e   = RelsUtils::nthElementOfTuple(tuple, 1);
      Node      reason  = (*mem_exp_it).second;

      if(areEqual(fst, fst_e) && areEqual(snd, snd_e)) {
        if( fst != fst_e) {
          reason = NodeManager::currentNM()->mkNode(kind::AND, reason, explain( NodeManager::currentNM()->mkNode(kind::EQUAL, fst, fst_e)) );
        }
        if( snd != snd_e) {
          reason = NodeManager::currentNM()->mkNode(kind::AND, reason, explain( NodeManager::currentNM()->mkNode(kind::EQUAL, snd, snd_e)) );
        }
        return reason;
      }
      ++mem_exp_it;
    }
    if(!ei->d_tc.get().isNull()) {
      Node      rel_rep = getRepresentative(ei->d_tc.get()[0]);
      EqcInfo*  rel_ei  = getOrMakeEqcInfo(rel_rep);
      if(rel_ei != NULL) {
        NodeMap::iterator rel_mem_exp_it = rel_ei->d_mem_exp.begin();
        while(rel_mem_exp_it != rel_ei->d_mem_exp.end()) {
          Node  exp     = rel_rep == ei->d_tc.get()[0] ? d_trueNode : explain(NodeManager::currentNM()->mkNode(kind::EQUAL,rel_rep, ei->d_tc.get()[0]));
          Node  tuple   = (*rel_mem_exp_it).first;
          Node  fst_e   = RelsUtils::nthElementOfTuple(tuple, 0);
          Node  snd_e   = RelsUtils::nthElementOfTuple(tuple, 1);

          if(areEqual(fst, fst_e) && areEqual(snd, snd_e)) {
            if( fst != fst_e) {
              exp = NodeManager::currentNM()->mkNode(kind::AND, exp, explain( NodeManager::currentNM()->mkNode(kind::EQUAL, fst, fst_e)) );
            }
            if( snd != snd_e) {
              exp = NodeManager::currentNM()->mkNode(kind::AND, exp, explain( NodeManager::currentNM()->mkNode(kind::EQUAL, snd, snd_e)) );
            }
            return NodeManager::currentNM()->mkNode(kind::AND, exp, (*rel_mem_exp_it).second);
          }
          ++rel_mem_exp_it;
        }
      }
    }
    Trace("rels-tc") << "End explainTCMem ############ pair = " << pair << std::endl;
    return Node::null();
  }

  void TheorySetsRels::sendTCInference(EqcInfo* tc_ei, std::hash_set<int> in_reachable, std::hash_set<int> out_reachable, Node mem_rep, Node fst_rep, Node snd_rep, int id1, int id2) {
    Trace("rels-std") << "Start making TC inference after adding a member " << mem_rep << " to " << tc_ei->d_tc.get() << std::endl;

    Node exp            = explainTCMem(tc_ei, mem_rep, fst_rep, snd_rep);
    Assert(!exp.isNull());
    sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, mem_rep, tc_ei->d_tc.get()), exp, "TC-Infer");
    std::hash_set<int>::iterator        in_reachable_it = in_reachable.begin();

    while(in_reachable_it != in_reachable.end()) {
      Node    in_node   = d_id_node[*in_reachable_it];
      Node    in_pair   = RelsUtils::constructPair(tc_ei->d_tc.get(), in_node, fst_rep);
      Node    new_pair  = RelsUtils::constructPair(tc_ei->d_tc.get(), in_node, snd_rep);
      Node    tc_exp    = explainTCMem(tc_ei, in_pair, in_node, fst_rep);
      Node    reason    =  tc_exp.isNull() ? exp : NodeManager::currentNM()->mkNode(kind::AND,tc_exp, exp);

      tc_ei->d_mem_exp[new_pair] = reason;
      tc_ei->d_mem.insert(new_pair);
      sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, new_pair, tc_ei->d_tc.get()), reason, "TC-Infer");
      in_reachable_it++;
    }

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
        reason  = NodeManager::currentNM()->mkNode(kind::AND,reason, in_pair_exp);
        tc_ei->d_mem_exp[new_pair] = reason;
        tc_ei->d_mem.insert(new_pair);
        sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, new_pair, tc_ei->d_tc.get()), reason, "TC-Infer");
        in_reachable_it++;
      }
      out_reachable_it++;
    }
  }

  void TheorySetsRels::collectReachableNodes(std::map< int, std::vector< int > >& id_map, int start_id, std::hash_set< int >& reachable_set, bool firstRound) {
    Trace("rels-std") << "****  Collecting reachable nodes for node with id " << start_id << std::endl;
    if(reachable_set.find(start_id) != reachable_set.end()) {
      return;
    }
    if(!firstRound) {
      reachable_set.insert(start_id);
    }

    std::vector< int > id_list              = getIdList(id_map, start_id);
    std::vector< int >::iterator id_list_it = id_list.begin();

    while( id_list_it != id_list.end() ) {
      collectReachableNodes( id_map, *id_list_it, reachable_set, false );
      id_list_it++;
    }
  }

  void TheorySetsRels::eqNotifyNewClass( Node n ) {
    Trace("rels-std") << "[sets-rels] eqNotifyNewClass:" << " t = " << n << std::endl;
    if(isRel(n) && (n.getKind() == kind::TRANSPOSE ||
                    n.getKind() == kind::PRODUCT ||
                    n.getKind() == kind::JOIN ||
                    n.getKind() == kind::TCLOSURE)) {
      getOrMakeEqcInfo( n, true );
    }
  }

  // Merge t2 into t1, t1 will be the rep of the new eqc
  void TheorySetsRels::eqNotifyPostMerge( Node t1, Node t2 ) {
    Trace("rels-std") << "[sets-rels] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;

    // Merge membership constraint with "true" or "false" eqc
    if( (t1 == d_trueNode || t1 == d_falseNode) && t2.getKind() == kind::MEMBER && t2[0].getType().isTuple() ) {

      Assert(t1 == d_trueNode || t1 == d_falseNode);
      bool      polarity        = t1 == d_trueNode;
      Node      t2_1rep         = getRepresentative(t2[1]);
      EqcInfo*  ei              = getOrMakeEqcInfo( t2_1rep, true );

      if( polarity ) {
        ei->d_mem.insert(t2[0]);
        ei->d_mem_exp[t2[0]] = explain(t2);
      }
      // Process a membership constraint that a tuple is a member of transpose of rel
      if( !ei->d_tp.get().isNull() ) {
        Node exp = polarity ? explain(t2) : explain(t2.negate());
        if(ei->d_tp.get() != t2[1]) {
          exp = NodeManager::currentNM()->mkNode(kind::AND, explain(NodeManager::currentNM()->mkNode(kind::EQUAL, ei->d_tp.get(), t2[1]) ), exp );
        }
        sendInferTranspose( polarity, t2[0], ei->d_tp.get(), exp, true );
      }
      // Process a membership constraint that a tuple is a member of product of rel
      if( !ei->d_pt.get().isNull() ) {
        Node exp = polarity ? explain(t2) : explain(t2.negate());
        if(ei->d_pt.get() != t2[1]) {
          exp = NodeManager::currentNM()->mkNode(kind::AND, explain(NodeManager::currentNM()->mkNode(kind::EQUAL, ei->d_pt.get(), t2[1]) ), exp );
        }
        sendInferProduct( polarity, t2[0], ei->d_pt.get(), exp );
      }
      // Process a membership constraint that a tuple is a member of transitive closure of rel
      if( polarity && !ei->d_tc.get().isNull() ) {
        addTCMemAndSendInfer( ei, t2, Node::null() );
      }

    // Merge two relation eqcs
    } else if( t1.getType().isSet() && t2.getType().isSet() && t1.getType().getSetElementType().isTuple() ) {
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
      if(!t1_ei->d_tc.get().isNull()) {
        NodeSet::const_iterator     mem_it  = t2_ei->d_mem.begin();
        while(mem_it != t2_ei->d_mem.end()) {
          addTCMemAndSendInfer(t1_ei, NodeManager::currentNM()->mkNode(kind::MEMBER,*mem_it, t1_ei->d_tc.get()), (*t2_ei->d_mem_exp.find(*mem_it)).second);
          mem_it++;
        }
      } else if(!t2_ei->d_tc.get().isNull()) {
        t1_ei->d_tc.set(t2_ei->d_tc);
        NodeSet::const_iterator     t1_mem_it  = t1_ei->d_mem.begin();

        while(t1_mem_it != t1_ei->d_mem.end()) {
          NodeMap::const_iterator       reason_it       = t1_ei->d_mem_exp.find(*t1_mem_it);
          Assert(reason_it != t1_ei->d_mem_exp.end());
          addTCMemAndSendInfer(t1_ei, NodeManager::currentNM()->mkNode(kind::MEMBER,*t1_mem_it, t1_ei->d_tc.get()), (*reason_it).second);
          t1_mem_it++;
        }

        NodeSet::const_iterator     t2_mem_it  = t2_ei->d_mem.begin();

        while(t2_mem_it != t2_ei->d_mem.end()) {
          addTCMemAndSendInfer(t1_ei, NodeManager::currentNM()->mkNode(kind::MEMBER,*t2_mem_it, t2_ei->d_tc.get()), (*t2_ei->d_mem_exp.find(*t2_mem_it)).second);
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
      // Apply Product rule on (non)members of t2 and t1->pt
      if(!t1_ei->d_pt.get().isNull()) {
        for(NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++) {
          if(!t1_ei->d_mem.contains(*itr)) {
            sendInferProduct( true, *itr, t1_ei->d_pt.get(), NodeManager::currentNM()->mkNode(kind::AND,explain(NodeManager::currentNM()->mkNode(kind::EQUAL,t1_ei->d_pt.get(), t2)), explain(NodeManager::currentNM()->mkNode(kind::MEMBER,*itr, t2))) );
          }
        }
      } else if(!t2_ei->d_pt.get().isNull()) {
        t1_ei->d_pt.set(t2_ei->d_pt);
        for(NodeSet::key_iterator itr = t1_ei->d_mem.key_begin(); itr != t1_ei->d_mem.key_end(); itr++) {
          if(!t2_ei->d_mem.contains(*itr)) {
            sendInferProduct( true, *itr, t2_ei->d_pt.get(), NodeManager::currentNM()->mkNode(kind::AND,explain(NodeManager::currentNM()->mkNode(kind::EQUAL,t1, t2_ei->d_pt.get())), explain(NodeManager::currentNM()->mkNode(kind::MEMBER,*itr, t1))) );
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
      if(t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull()) {
        t1_ei->d_pt.set(t2_ei->d_pt);
        for(NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++) {
          t1_ei->d_mem.insert(*itr);
          t1_ei->d_mem_exp.insert(*itr, t2_ei->d_mem_exp[*itr]);
        }
      }
    }
  }

  void TheorySetsRels::mergeTransposeEqcs( Node t1, Node t2 ) {
    Trace("rels-std") << "[sets-rels] Merge TRANSPOSE eqcs t1 = " << t1 << " and t2 = " << t2 << std::endl;
    EqcInfo* t1_ei = getOrMakeEqcInfo( t1 );
    EqcInfo* t2_ei = getOrMakeEqcInfo( t2 );

    if( t1_ei != NULL && t2_ei != NULL ) {
      Trace("rels-std") << "[sets-rels] 0 Merge TRANSPOSE eqcs t1 = " << t1 << " and t2 = " << t2 << std::endl;
      // TP(t1) = TP(t2) -> t1 = t2;
      if( !t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull() ) {
        sendInferTranspose( true, t1_ei->d_tp.get(), t2_ei->d_tp.get(), explain(NodeManager::currentNM()->mkNode(kind::EQUAL,t1, t2)) );
      }
      // Apply transpose rule on (non)members of t2 and t1->tp
      if( !t1_ei->d_tp.get().isNull() ) {
        for( NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++ ) {
          if( !t1_ei->d_mem.contains( *itr ) ) {
            sendInferTranspose( true, *itr, t1_ei->d_tp.get(), NodeManager::currentNM()->mkNode(kind::AND, explain(NodeManager::currentNM()->mkNode(kind::EQUAL,t1_ei->d_tp.get(), t2)), explain(NodeManager::currentNM()->mkNode(kind::MEMBER,*itr, t2))) );
          }
        }
        // Apply transpose rule on members of t1 and t2->tp
      } else if( !t2_ei->d_tp.get().isNull() ) {
        t1_ei->d_tp.set( t2_ei->d_tp );
        for( NodeSet::key_iterator itr = t1_ei->d_mem.key_begin(); itr != t1_ei->d_mem.key_end(); itr++ ) {
          if( !t2_ei->d_mem.contains(*itr) ) {
            sendInferTranspose( true, *itr, t2_ei->d_tp.get(), NodeManager::currentNM()->mkNode(kind::AND, explain(NodeManager::currentNM()->mkNode(kind::EQUAL,t1, t2_ei->d_tp.get())), explain(NodeManager::currentNM()->mkNode(kind::MEMBER,*itr, t1))) );
          }
        }
      }
    // t1 was created already and t2 was not
    } else if(t1_ei != NULL) {
      if( t1_ei->d_tp.get().isNull() && t2.getKind() == kind::TRANSPOSE ) {
        t1_ei->d_tp.set( t2 );
      }
    } else if( t2_ei != NULL ){
      t1_ei = getOrMakeEqcInfo( t1, true );
      if( t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull() ) {
        t1_ei->d_tp.set( t2_ei->d_tp );
        for( NodeSet::key_iterator itr = t2_ei->d_mem.key_begin(); itr != t2_ei->d_mem.key_end(); itr++ ) {
          t1_ei->d_mem.insert( *itr );
          t1_ei->d_mem_exp.insert( *itr, t2_ei->d_mem_exp[*itr] );
        }
      }
    }
  }

  void TheorySetsRels::doPendingMerge() {
    for( NodeList::const_iterator itr = d_pending_merge.begin(); itr != d_pending_merge.end(); itr++ ) {
      if( !holds(*itr) ) {
        if( d_lemmas_produced.find(*itr)==d_lemmas_produced.end() ) {
          Trace("rels-lemma") << "[std-sets-rels-lemma] Send out a merge fact as lemma: "
                              << *itr << std::endl;
          d_sets_theory.d_out->lemma( *itr );
          d_lemmas_produced.insert(*itr);
        }
      }
    }
  }

  void TheorySetsRels::sendInferTranspose( bool polarity, Node t1, Node t2, Node exp, bool reverseOnly ) {
    Assert( t2.getKind() == kind::TRANSPOSE );
    if( !polarity ) {
      return;
    }
    if( polarity && isRel(t1) && isRel(t2) ) {
      Assert(t1.getKind() == kind::TRANSPOSE);
      sendMergeInfer(NodeManager::currentNM()->mkNode(kind::EQUAL, t1[0], t2[0]), exp, "Transpose-Equal");
      return;
    }

    if( reverseOnly ) {
      sendMergeInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::reverseTuple(t1), t2[0]), exp, "Transpose-Rule" );
    } else {
      sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, t1, t2), exp, "Transpose-Rule");
      sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::reverseTuple(t1), t2[0]), exp, "Transpose-Rule");
    }
  }

  void TheorySetsRels::sendMergeInfer( Node fact, Node reason, const char * c ) {
    if( !holds( fact ) ) {
      Node lemma = NodeManager::currentNM()->mkNode( kind::IMPLIES, reason, fact);
      d_pending_merge.push_back(lemma);
      Trace("std-rels") << "[std-rels-lemma] Generate a lemma by applying " << c
                        << ": " << lemma << std::endl;
    }
  }

  void TheorySetsRels::sendInferProduct( bool polarity, Node member, Node pt_rel, Node exp ) {
    Assert( pt_rel.getKind() == kind::PRODUCT );

    if(!polarity) {
      return;
    }

    std::vector<Node>   r1_element;
    std::vector<Node>   r2_element;
    Node                r1      = pt_rel[0];
    Node                r2      = pt_rel[1];
    Datatype            dt      = r1.getType().getSetElementType().getDatatype();
    unsigned int        i       = 0;
    unsigned int        s1_len  = r1.getType().getSetElementType().getTupleLength();
    unsigned int        tup_len = pt_rel.getType().getSetElementType().getTupleLength();

    r1_element.push_back(Node::fromExpr(dt[0].getConstructor()));
    for( ; i < s1_len; ++i ) {
      r1_element.push_back( RelsUtils::nthElementOfTuple( member, i ) );
    }

    dt = r2.getType().getSetElementType().getDatatype();
    r2_element.push_back( Node::fromExpr( dt[0].getConstructor() ) );
    for( ; i < tup_len; ++i ) {
      r2_element.push_back( RelsUtils::nthElementOfTuple(member, i) );
    }

    Node tuple_1 = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, r1_element );
    Node tuple_2 = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, r2_element );
    sendMergeInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, tuple_1, r1), exp, "Product-Split" );
    sendMergeInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, tuple_2, r2), exp, "Product-Split" );
  }

  TheorySetsRels::EqcInfo* TheorySetsRels::getOrMakeEqcInfo( Node n, bool doMake ){
    std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
    if( eqc_i == d_eqc_info.end() ){
      if( doMake ){
        EqcInfo* ei;
        if( eqc_i!=d_eqc_info.end() ){
          ei = eqc_i->second;
        }else{
          ei = new EqcInfo(d_sets_theory.getSatContext());
          d_eqc_info[n] = ei;
        }
        if( n.getKind() == kind::TRANSPOSE ){
          ei->d_tp = n;
        } else if( n.getKind() == kind::PRODUCT ) {
          ei->d_pt = n;
        } else if( n.getKind() == kind::TCLOSURE ) {
          ei->d_tc = n;
        } else if( n.getKind() == kind::JOIN ) {
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

  void TheorySetsRels::printNodeMap(char* fst, char* snd, NodeMap map) {
    NodeMap::iterator map_it    = map.begin();
    while(map_it != map.end()) {
      Trace("rels-debug") << fst << " "<< (*map_it).first << " " << snd << " " << (*map_it).second<< std::endl;
      map_it++;
    }
  }

  bool TheorySetsRels::addId( std::map< int, std::vector< int > >& id_map, int key, int id ) {
    int n_data = d_vec_size[key];
    int len    = n_data < (int)id_map[key].size() ? n_data : id_map[key].size();

    for( int i = 0; i < len; i++ ) {
      if( id_map[key][i] == id) {
        return false;
      }
    }
    if( n_data < (int)id_map[key].size() ) {
      id_map[key][n_data] = id;
    } else {
      id_map[key].push_back( id );
    }
    d_vec_size[key] = n_data+1;
    return true;
  }

  std::vector< int > TheorySetsRels::getIdList( std::map< int, std::vector< int > >& id_map, int key ) {
    std::vector< int > id_list;
    int n_data = d_vec_size[key];
    int len    = n_data < (int)id_map[key].size() ? n_data : id_map[key].size();

    for( int i = 0; i < len; i++ ) {
      id_list.push_back(id_map[key][i]);
    }
    return id_list;
  }

}
}
}













