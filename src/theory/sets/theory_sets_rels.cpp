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
          if( tp_terms.size() > 0 ) {
            applyTransposeRule( tp_terms );
            applyTransposeRule( tp_terms[0], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::JOIN) != kind_terms.end() ) {
          std::vector<Node> join_terms = kind_terms[kind::JOIN];
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
        if( kind_terms.find(kind::JOIN_IMAGE) != kind_terms.end() ) {
          std::vector<Node> join_image_terms = kind_terms[kind::JOIN_IMAGE];
          for( unsigned int j = 0; j < join_image_terms.size(); j++ ) {
            applyJoinImageRule( mem, join_image_terms[j], exp );
          }
        }
        if( kind_terms.find(kind::IDEN) != kind_terms.end() ) {
          std::vector<Node> iden_terms = kind_terms[kind::IDEN];
          for( unsigned int j = 0; j < iden_terms.size(); j++ ) {
            applyIdenRule( mem, iden_terms[j], exp );
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
          } else if( k_t_it->first == kind::JOIN_IMAGE ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              computeMembersForJoinImageTerm( *term_it );
              term_it++;
            }
          } else if( k_t_it->first == kind::IDEN ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              computeMembersForIdenTerm( *term_it );
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

      Trace("rels-ee") << "[sets-rels-ee] Eqc term representative: " << eqc_rep << " with type " << eqc_rep.getType() << std::endl;

      while( !eqc_i.isFinished() ){
        Node eqc_node = (*eqc_i);

        Trace("rels-ee") << "  term : " << eqc_node << std::endl;

        if( getRepresentative(eqc_rep) == getRepresentative(d_trueNode) ||
            getRepresentative(eqc_rep) == getRepresentative(d_falseNode) ) {

          // collect membership info
          if( eqc_node.getKind() == kind::MEMBER && eqc_node[1].getType().getSetElementType().isTuple()) {
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
            }
          }
        // collect relational terms info
        } else if( eqc_rep.getType().isSet() && eqc_rep.getType().getSetElementType().isTuple() ) {
          if( eqc_node.getKind() == kind::TRANSPOSE || eqc_node.getKind() == kind::JOIN ||
              eqc_node.getKind() == kind::PRODUCT || eqc_node.getKind() == kind::TCLOSURE ||
              eqc_node.getKind() == kind::JOIN_IMAGE || eqc_node.getKind() == kind::IDEN ) {
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

  /* JOIN-IMAGE UP  :   (x, x1) IS_IN R, ..., (x, xn) IS_IN R  (R JOIN_IMAGE n)
  *                     -------------------------------------------------------
  *                     x IS_IN (R JOIN_IMAGE n) || NOT DISTINCT(x1, ... , xn)
  *
  */

  void TheorySetsRels::computeMembersForJoinImageTerm( Node join_image_term ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** Compute members for JoinImage Term = " << join_image_term << std::endl;
    MEM_IT rel_mem_it = d_rReps_memberReps_cache.find( getRepresentative( join_image_term[0] ) );

    if( rel_mem_it == d_rReps_memberReps_cache.end() ) {
      return;
    }

    Node join_image_rel = join_image_term[0];
    std::hash_set< Node, NodeHashFunction > hasChecked;
    Node join_image_rel_rep = getRepresentative( join_image_rel );
    std::vector< Node >::iterator mem_rep_it = (*rel_mem_it).second.begin();
    MEM_IT rel_mem_exp_it = d_rReps_memberReps_exp_cache.find( join_image_rel_rep );
    std::vector< Node >::iterator mem_rep_exp_it = (*rel_mem_exp_it).second.begin();
    unsigned int min_card = join_image_term[1].getConst<Rational>().getNumerator().getUnsignedInt();

    while( mem_rep_it != (*rel_mem_it).second.end() ) {
      Node fst_mem_rep = RelsUtils::nthElementOfTuple( *mem_rep_it, 0 );

      if( hasChecked.find( fst_mem_rep ) != hasChecked.end() ) {
        ++mem_rep_it;
        ++mem_rep_exp_it;
        continue;
      }
      hasChecked.insert( fst_mem_rep );

      Datatype dt = join_image_term.getType().getSetElementType().getDatatype();
      Node new_membership = NodeManager::currentNM()->mkNode(kind::MEMBER,
                                                             NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR,
                                                                                               Node::fromExpr(dt[0].getConstructor()), fst_mem_rep ),
                                                             join_image_term);
      if( holds( new_membership ) ) {
        ++mem_rep_it;
        ++mem_rep_exp_it;
        continue;
      }

      std::vector< Node > reasons;
      std::vector< Node > existing_members;
      std::vector< Node >::iterator mem_rep_exp_it_snd = (*rel_mem_exp_it).second.begin();

      while( mem_rep_exp_it_snd != (*rel_mem_exp_it).second.end() ) {
        Node fst_element_snd_mem = RelsUtils::nthElementOfTuple( (*mem_rep_exp_it_snd)[0], 0 );

        if( areEqual( fst_mem_rep,  fst_element_snd_mem ) ) {
          bool notExist = true;
          std::vector< Node >::iterator existing_mem_it = existing_members.begin();
          Node snd_element_snd_mem = RelsUtils::nthElementOfTuple( (*mem_rep_exp_it_snd)[0], 1 );

          while( existing_mem_it != existing_members.end() ) {
            if( areEqual( (*existing_mem_it), snd_element_snd_mem ) ) {
              notExist = false;
              break;
            }
            ++existing_mem_it;
          }

          if( notExist ) {
            existing_members.push_back( snd_element_snd_mem );
            reasons.push_back( *mem_rep_exp_it_snd );
            if( fst_mem_rep != fst_element_snd_mem ) {
              reasons.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, fst_mem_rep, fst_element_snd_mem ) );
            }
            if( join_image_rel != (*mem_rep_exp_it_snd)[1] ) {
              reasons.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, (*mem_rep_exp_it_snd)[1], join_image_rel ));
            }
            if( existing_members.size() == min_card ) {
              if( min_card >= 2) {
                new_membership = NodeManager::currentNM()->mkNode( kind::OR, new_membership, NodeManager::currentNM()->mkNode( kind::NOT, NodeManager::currentNM()->mkNode( kind::DISTINCT, existing_members ) ));
              }
              Assert(reasons.size() >= 1);
              sendInfer( new_membership, reasons.size() > 1 ? NodeManager::currentNM()->mkNode( kind::AND, reasons) : reasons[0], "JOIN-IMAGE UP" );
              break;
            }
          }
        }
        ++mem_rep_exp_it_snd;
      }
      ++mem_rep_it;
      ++mem_rep_exp_it;
    }
    Trace("rels-debug") << "\n[Theory::Rels] *********** Done with computing members for JoinImage Term" << join_image_term << "*********** " << std::endl;
  }

  /* JOIN-IMAGE DOWN  : (x) IS_IN (R JOIN_IMAGE n)
  *                     -------------------------------------------------------
  *                     (x, x1) IS_IN R .... (x, xn) IS_IN R  DISTINCT(x1, ... , xn)
  *
  */

  void TheorySetsRels::applyJoinImageRule( Node mem_rep, Node join_image_term, Node exp ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** applyJoinImageRule on " << join_image_term
                        << " with mem_rep = " << mem_rep  << " and exp = " << exp << std::endl;
    if( d_rel_nodes.find( join_image_term ) == d_rel_nodes.end() ) {
      computeMembersForJoinImageTerm( join_image_term );
      d_rel_nodes.insert( join_image_term );
    }

    Node join_image_rel = join_image_term[0];
    Node join_image_rel_rep = getRepresentative( join_image_rel );
    MEM_IT rel_mem_it = d_rReps_memberReps_cache.find( join_image_rel_rep );
    unsigned int min_card = join_image_term[1].getConst<Rational>().getNumerator().getUnsignedInt();

    if( rel_mem_it != d_rReps_memberReps_cache.end() ) {
      if( d_membership_trie.find( join_image_rel_rep ) != d_membership_trie.end() ) {
        computeTupleReps( mem_rep );
        if( d_membership_trie[join_image_rel_rep].findSuccessors(d_tuple_reps[mem_rep]).size() >= min_card ) {
          return;
        }
      }
    }

    Node reason = exp;
    Node conclusion = d_trueNode;
    std::vector< Node > distinct_skolems;
    Node fst_mem_element = RelsUtils::nthElementOfTuple( exp[0], 0 );

    if( exp[1] != join_image_term ) {
      reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode( kind::EQUAL, exp[1], join_image_term ) );
    }
    for( unsigned int i = 0; i < min_card; i++ ) {
      Node skolem = NodeManager::currentNM()->mkSkolem( "jig", join_image_rel.getType()[0].getTupleTypes()[0] );
      distinct_skolems.push_back( skolem );
      conclusion = NodeManager::currentNM()->mkNode( kind::AND, conclusion, NodeManager::currentNM()->mkNode( kind::MEMBER, RelsUtils::constructPair( join_image_rel, fst_mem_element, skolem ), join_image_rel ) );
    }
    if( distinct_skolems.size() >= 2 ) {
      conclusion =  NodeManager::currentNM()->mkNode( kind::AND, conclusion, NodeManager::currentNM()->mkNode( kind::DISTINCT, distinct_skolems ) );
    }
    sendInfer( conclusion, reason, "JOIN-IMAGE DOWN" );
    Trace("rels-debug") << "\n[Theory::Rels] *********** Done with applyJoinImageRule ***********" << std::endl;

  }


  /* IDENTITY-DOWN  : (x, y) IS_IN IDEN(R)
  *               -------------------------------------------------------
  *                   x = y,  (x IS_IN R)
  *
  */

  void TheorySetsRels::applyIdenRule( Node mem_rep, Node iden_term, Node exp) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** applyIdenRule on " << iden_term
                        << " with mem_rep = " << mem_rep  << " and exp = " << exp << std::endl;
    if( d_rel_nodes.find( iden_term ) == d_rel_nodes.end() ) {
      computeMembersForIdenTerm( iden_term );
      d_rel_nodes.insert( iden_term );
    }
    Node reason = exp;
    Node fst_mem = RelsUtils::nthElementOfTuple( exp[0], 0 );
    Node snd_mem = RelsUtils::nthElementOfTuple( exp[0], 1 );
    Datatype dt = iden_term[0].getType().getSetElementType().getDatatype();
    Node fact = NodeManager::currentNM()->mkNode( kind::MEMBER, NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, Node::fromExpr(dt[0].getConstructor()), fst_mem ), iden_term[0] );

    if( exp[1] != iden_term ) {
      reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode( kind::EQUAL, exp[1], iden_term ) );
    }
    sendInfer( NodeManager::currentNM()->mkNode( kind::AND, fact, NodeManager::currentNM()->mkNode( kind::EQUAL, fst_mem, snd_mem ) ), reason, "IDENTITY-DOWN" );
    Trace("rels-debug") << "\n[Theory::Rels] *********** Done with applyIdenRule on " << iden_term << std::endl;
  }

  /* IDEN UP  : (x) IS_IN R        IDEN(R) IN T
  *             --------------------------------
  *                   (x, x) IS_IN IDEN(R)
  *
  */

  void TheorySetsRels::computeMembersForIdenTerm( Node iden_term ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** Compute members for Iden Term = " << iden_term << std::endl;
    Node iden_term_rel = iden_term[0];
    Node iden_term_rel_rep = getRepresentative( iden_term_rel );

    if( d_rReps_memberReps_cache.find( iden_term_rel_rep ) == d_rReps_memberReps_cache.end() ) {
      return;
    }

    MEM_IT rel_mem_exp_it = d_rReps_memberReps_exp_cache.find( iden_term_rel_rep );
    std::vector< Node >::iterator mem_rep_exp_it = (*rel_mem_exp_it).second.begin();

    while( mem_rep_exp_it != (*rel_mem_exp_it).second.end() ) {
      Node reason = *mem_rep_exp_it;
      Node fst_exp_mem = RelsUtils::nthElementOfTuple( (*mem_rep_exp_it)[0], 0 );
      Node new_mem = RelsUtils::constructPair( iden_term, fst_exp_mem, fst_exp_mem );

      if( (*mem_rep_exp_it)[1] != iden_term_rel ) {
        reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode( kind::EQUAL, (*mem_rep_exp_it)[1], iden_term_rel ) );
      }
      sendInfer( NodeManager::currentNM()->mkNode( kind::MEMBER, new_mem, iden_term ), reason, "IDENTITY-UP" );
      ++mem_rep_exp_it;
    }
    Trace("rels-debug") << "\n[Theory::Rels] *********** Done with computing members for Iden Term = " << iden_term << std::endl;
  }


  /*
   * Construct transitive closure graph for tc_rep based on the members of tc_r_rep
   */

  /*
   * TCLOSURE TCLOSURE(x) = x | x.x | x.x.x | ... (| is union)
   *
   * TCLOSURE-UP I:   (a, b) IS_IN x            TCLOSURE(x) in T
   *              ---------------------------------------------
   *                              (a, b) IS_IN TCLOSURE(x)
   *
   *
   *
   * TCLOSURE-UP II : (a, b) IS_IN TCLOSURE(x)  (b, c) IS_IN TCLOSURE(x)
   *              -----------------------------------------------------------
   *                            (a, c) IS_IN TCLOSURE(x)
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
        Node new_pair = RelsUtils::constructPair( tc_rel, cur_node_rep, *set_it );
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
      reason = NodeManager::currentNM()->mkNode(kind::AND, exp, NodeManager::currentNM()->mkNode(kind::EQUAL, pt_rel, exp[1]));
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
   * transpose-occur rule:    (a, b) IS_IN X   (TRANSPOSE X) in T
   *                         ---------------------------------------
   *                            (b, a) IS_IN (TRANSPOSE X)
   *
   * transpose-reverse rule:    (a, b) IS_IN (TRANSPOSE X)
   *                         ---------------------------------------
   *                            (b, a) IS_IN X
   *
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
    d_eqEngine->addFunctionKind(kind::JOIN_IMAGE);
    d_eqEngine->addFunctionKind(kind::IDEN);
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

  std::vector<Node> TupleTrie::findSuccessors( std::vector< Node >& reps, int argIndex ) {
    std::vector<Node>   nodes;
    std::map< Node, TupleTrie >::iterator it;

    if( argIndex==(int)reps.size() ){
      it = d_data.begin();
      while(it != d_data.end()) {
        nodes.push_back(it->first);
        it++;
      }
      return nodes;
    }else{
      it = d_data.find( reps[argIndex] );
      if( it==d_data.end() ){
        return nodes;
      }else{
        return it->second.findSuccessors( reps, argIndex+1 );
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

  TheorySetsRels::EqcInfo::EqcInfo( context::Context* c ) :
  d_mem(c), d_mem_exp(c), d_tp(c), d_pt(c), d_tc(c), d_rel_tc(c) {}

  void TheorySetsRels::eqNotifyNewClass( Node n ) {
    Trace("rels-std") << "[sets-rels] eqNotifyNewClass:" << " t = " << n << std::endl;
    if(n.getKind() == kind::TRANSPOSE || n.getKind() == kind::PRODUCT || n.getKind() == kind::TCLOSURE) {
      getOrMakeEqcInfo( n, true );
      if( n.getKind() == kind::TCLOSURE ) {
        Node relRep_of_tc = getRepresentative( n[0] );
        EqcInfo*  rel_ei = getOrMakeEqcInfo( relRep_of_tc, true );

        if( rel_ei->d_rel_tc.get().isNull() ) {
          rel_ei->d_rel_tc = n;
          Node exp = relRep_of_tc == n[0] ? d_trueNode : NodeManager::currentNM()->mkNode( kind::EQUAL, relRep_of_tc, n[0] );
          for( NodeSet::const_iterator mem_it = rel_ei->d_mem.begin(); mem_it != rel_ei->d_mem.end(); mem_it++ ) {
            Node mem_exp = (*rel_ei->d_mem_exp.find(*mem_it)).second;
            exp = NodeManager::currentNM()->mkNode( kind::AND, exp, mem_exp);
            if( mem_exp[1] != relRep_of_tc ) {
              exp = NodeManager::currentNM()->mkNode( kind::AND, exp, NodeManager::currentNM()->mkNode(kind::EQUAL, relRep_of_tc, mem_exp[1] ) );
            }
            sendMergeInfer( NodeManager::currentNM()->mkNode(kind::MEMBER, mem_exp[0], n), exp, "TCLOSURE-UP I" );
          }
        }
      }
    }
  }

  // Merge t2 into t1, t1 will be the rep of the new eqc
  void TheorySetsRels::eqNotifyPostMerge( Node t1, Node t2 ) {
    Trace("rels-std") << "[sets-rels-std] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;

    // Merge membership constraint with "true" eqc
    if( t1 == d_trueNode && t2.getKind() == kind::MEMBER && t2[0].getType().isTuple() ) {
      Node      mem_rep  = getRepresentative( t2[0] );
      Node      t2_1rep  = getRepresentative( t2[1] );
      EqcInfo*  ei       = getOrMakeEqcInfo( t2_1rep, true );
      if(ei->d_mem.contains(mem_rep)) {
        return;
      }
      Node exp = t2;

      ei->d_mem.insert( mem_rep );
      ei->d_mem_exp.insert( mem_rep, exp );

      // Process a membership constraint that a tuple is a member of transpose of rel
      if( !ei->d_tp.get().isNull() ) {
        if( ei->d_tp.get() != t2[1] ) {
          exp = NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::EQUAL, ei->d_tp.get(), t2[1]), t2 );
        }
        sendInferTranspose( t2[0], ei->d_tp.get(), exp );
      }
      // Process a membership constraint that a tuple is a member of product of rel
      if( !ei->d_pt.get().isNull() ) {
        if( ei->d_pt.get() != t2[1] ) {
          exp = NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::EQUAL, ei->d_pt.get(), t2[1]), t2 );
        }
        sendInferProduct( t2[0], ei->d_pt.get(), exp );
      }

      if( !ei->d_rel_tc.get().isNull() ) {
        if( ei->d_rel_tc.get()[0] != t2[1] ) {
          exp = NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::EQUAL, ei->d_rel_tc.get()[0], t2[1]), t2 );
        }
        sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, t2[0], ei->d_rel_tc.get()), exp, "TCLOSURE-UP I");
      }
      // Process a membership constraint that a tuple is a member of transitive closure of rel
      if( !ei->d_tc.get().isNull() ) {
        sendInferTClosure( t2, ei );
      }

    // Merge two relation eqcs
    } else if( t1.getType().isSet() && t2.getType().isSet() && t1.getType().getSetElementType().isTuple() ) {
      EqcInfo* t1_ei = getOrMakeEqcInfo( t1 );
      EqcInfo* t2_ei = getOrMakeEqcInfo( t2 );

      if( t1_ei != NULL && t2_ei != NULL ) {
        if( !t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull() ) {
          sendInferTranspose(t1_ei->d_tp.get(), t2_ei->d_tp.get(), NodeManager::currentNM()->mkNode(kind::EQUAL, t1_ei->d_tp.get(), t2_ei->d_tp.get() ) );
        }
        std::vector< Node > t2_new_mems;
        std::vector< Node > t2_new_exps;
        NodeSet::const_iterator t2_mem_it = t2_ei->d_mem.begin();
        NodeSet::const_iterator t1_mem_it = t1_ei->d_mem.begin();

        for( ; t2_mem_it != t2_ei->d_mem.end(); t2_mem_it++ ) {
          if( !t1_ei->d_mem.contains( *t2_mem_it ) ) {
            Node t2_mem_exp = (*t2_ei->d_mem_exp.find(*t2_mem_it)).second;

            if( t2_ei->d_tp.get().isNull() && !t1_ei->d_tp.get().isNull() ) {
              Node reason = t1_ei->d_tp.get() == (t2_mem_exp)[1]
                            ? (t2_mem_exp) : NodeManager::currentNM()->mkNode(kind::AND, t2_mem_exp, NodeManager::currentNM()->mkNode(kind::EQUAL, (t2_mem_exp)[1], t1_ei->d_tp.get()));
              sendInferTranspose( t2_mem_exp[0], t1_ei->d_tp.get(), reason );
            }
            if( t2_ei->d_pt.get().isNull() && !t1_ei->d_pt.get().isNull() ) {
              Node reason = t1_ei->d_pt.get() == (t2_mem_exp)[1]
                            ? (t2_mem_exp) : NodeManager::currentNM()->mkNode(kind::AND, t2_mem_exp, NodeManager::currentNM()->mkNode(kind::EQUAL, (t2_mem_exp)[1], t1_ei->d_pt.get()));
              sendInferProduct( t2_mem_exp[0], t1_ei->d_pt.get(), reason );
            }
            if( t2_ei->d_tc.get().isNull() && !t1_ei->d_tc.get().isNull() ) {
              sendInferTClosure( t2_mem_exp, t1_ei );
            }
            if( t2_ei->d_rel_tc.get().isNull() && !t1_ei->d_rel_tc.get().isNull() ) {
              Node reason = t1_ei->d_rel_tc.get()[0] == t2_mem_exp[1] ?
                            t2_mem_exp : NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::EQUAL, t1_ei->d_rel_tc.get()[0], t2_mem_exp[1]), t2_mem_exp );
              sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, t2_mem_exp[0], t1_ei->d_rel_tc.get()), reason, "TCLOSURE-UP I");
            }
            t2_new_mems.push_back( *t2_mem_it );
            t2_new_exps.push_back( t2_mem_exp );
          }
        }
        for( ; t1_mem_it != t1_ei->d_mem.end(); t1_mem_it++ ) {
          if( !t2_ei->d_mem.contains( *t1_mem_it ) ) {
            Node t1_mem_exp = (*t1_ei->d_mem_exp.find(*t1_mem_it)).second;
            if( t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull() ) {
              Node reason = t2_ei->d_tp.get() == (t1_mem_exp)[1]
                            ? (t1_mem_exp) : NodeManager::currentNM()->mkNode(kind::AND, t1_mem_exp, NodeManager::currentNM()->mkNode(kind::EQUAL, (t1_mem_exp)[1], t2_ei->d_tp.get()));
              sendInferTranspose( (t1_mem_exp)[0], t2_ei->d_tp.get(), reason );
            }
            if( t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull() ) {
              Node reason = t2_ei->d_pt.get() == (t1_mem_exp)[1]
                            ? (t1_mem_exp) : NodeManager::currentNM()->mkNode(kind::AND, t1_mem_exp, NodeManager::currentNM()->mkNode(kind::EQUAL, (t1_mem_exp)[1], t2_ei->d_pt.get()));
              sendInferProduct( (t1_mem_exp)[0], t2_ei->d_pt.get(), reason );
            }
            if( t1_ei->d_tc.get().isNull() && !t2_ei->d_tc.get().isNull() ) {
              sendInferTClosure(t1_mem_exp, t2_ei );
            }
            if( t1_ei->d_rel_tc.get().isNull() && !t2_ei->d_rel_tc.get().isNull() ) {
              Node reason = t2_ei->d_rel_tc.get()[0] == t1_mem_exp[1] ?
                            t1_mem_exp : NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::EQUAL, t2_ei->d_rel_tc.get()[0], t1_mem_exp[1]), t1_mem_exp );
              sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, t1_mem_exp[0], t2_ei->d_rel_tc.get()), reason, "TCLOSURE-UP I");
            }
          }
        }
        std::vector< Node >::iterator t2_new_mem_it = t2_new_mems.begin();
        std::vector< Node >::iterator t2_new_exp_it = t2_new_exps.begin();
        for( ; t2_new_mem_it != t2_new_mems.end(); t2_new_mem_it++, t2_new_exp_it++ ) {
          t1_ei->d_mem.insert( *t2_new_mem_it );
          t1_ei->d_mem_exp.insert( *t2_new_mem_it, *t2_new_exp_it );
        }
        if( t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull() ) {
          t1_ei->d_tp.set(t2_ei->d_tp.get());
        }
        if( t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull() ) {
          t1_ei->d_pt.set(t2_ei->d_pt.get());
        }
        if( t1_ei->d_tc.get().isNull() && !t2_ei->d_tc.get().isNull() ) {
          t1_ei->d_tc.set(t2_ei->d_tc.get());
        }
        if( t1_ei->d_rel_tc.get().isNull() && !t2_ei->d_rel_tc.get().isNull() ) {
          t1_ei->d_rel_tc.set(t2_ei->d_rel_tc.get());
        }
      } else if( t1_ei != NULL ) {
        if( (t2.getKind() == kind::TRANSPOSE && t1_ei->d_tp.get().isNull()) ||
            (t2.getKind() == kind::PRODUCT && t1_ei->d_pt.get().isNull()) ||
            (t2.getKind() == kind::TCLOSURE && t1_ei->d_tc.get().isNull()) ) {
          NodeSet::const_iterator t1_mem_it = t1_ei->d_mem.begin();

          if( t2.getKind() == kind::TRANSPOSE ) {
            t1_ei->d_tp = t2;
          } else if( t2.getKind() == kind::PRODUCT ) {
            t1_ei->d_pt = t2;
          } else if( t2.getKind() == kind::TCLOSURE ) {
            t1_ei->d_tc = t2;
          }
          for( ; t1_mem_it != t1_ei->d_mem.end(); t1_mem_it++ ) {
            Node t1_exp = (*t1_ei->d_mem_exp.find(*t1_mem_it)).second;
            if( t2.getKind() == kind::TRANSPOSE ) {
              Node reason = t2 == t1_exp[1]
                            ? (t1_exp) : NodeManager::currentNM()->mkNode(kind::AND, (t1_exp), NodeManager::currentNM()->mkNode(kind::EQUAL, (t1_exp)[1], t2));
              sendInferTranspose( (t1_exp)[0], t2, reason );
            } else if( t2.getKind() == kind::PRODUCT ) {
              Node reason = t2 == (t1_exp)[1]
                            ? (t1_exp) : NodeManager::currentNM()->mkNode(kind::AND, (t1_exp), NodeManager::currentNM()->mkNode(kind::EQUAL, (t1_exp)[1], t2));
              sendInferProduct( (t1_exp)[0], t2, reason );
            } else if( t2.getKind() == kind::TCLOSURE ) {
              sendInferTClosure( t1_exp, t1_ei );
            }
          }
        }
      } else if( t2_ei != NULL ) {
        EqcInfo* new_t1_ei = getOrMakeEqcInfo( t1, true );
        if( new_t1_ei->d_tp.get().isNull() && !t2_ei->d_tp.get().isNull() ) {
          new_t1_ei->d_tp.set(t2_ei->d_tp.get());
        }
        if( new_t1_ei->d_pt.get().isNull() && !t2_ei->d_pt.get().isNull() ) {
          new_t1_ei->d_pt.set(t2_ei->d_pt.get());
        }
        if( new_t1_ei->d_tc.get().isNull() && !t2_ei->d_tc.get().isNull() ) {
          new_t1_ei->d_tc.set(t2_ei->d_tc.get());
        }
        if( new_t1_ei->d_rel_tc.get().isNull() && !t2_ei->d_rel_tc.get().isNull() ) {
          new_t1_ei->d_rel_tc.set(t2_ei->d_rel_tc.get());
        }
        if( (t1.getKind() == kind::TRANSPOSE && t2_ei->d_tp.get().isNull()) ||
            (t1.getKind() == kind::PRODUCT && t2_ei->d_pt.get().isNull()) ||
            (t1.getKind() == kind::TCLOSURE && t2_ei->d_tc.get().isNull()) ) {
          NodeSet::const_iterator t2_mem_it = t2_ei->d_mem.begin();

          for( ; t2_mem_it != t2_ei->d_mem.end(); t2_mem_it++ ) {
            Node t2_exp = (*t1_ei->d_mem_exp.find(*t2_mem_it)).second;

            if( t1.getKind() == kind::TRANSPOSE ) {
              Node reason = t1 == (t2_exp)[1]
                            ? (t2_exp) : NodeManager::currentNM()->mkNode(kind::AND, (t2_exp), NodeManager::currentNM()->mkNode(kind::EQUAL, (t2_exp)[1], t1));
              sendInferTranspose( (t2_exp)[0], t1, reason );
            } else if( t1.getKind() == kind::PRODUCT ) {
              Node reason = t1 == (t2_exp)[1]
                            ? (t2_exp) : NodeManager::currentNM()->mkNode(kind::AND, (t2_exp), NodeManager::currentNM()->mkNode(kind::EQUAL, (t2_exp)[1], t1));
              sendInferProduct( (t2_exp)[0], t1, reason );
            } else if( t1.getKind() == kind::TCLOSURE ) {
              sendInferTClosure( t2_exp, new_t1_ei );
            }
          }
        }
      }
    }

    Trace("rels-std") << "[sets-rels] done with eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  }

  void TheorySetsRels::sendInferTClosure( Node new_mem_exp, EqcInfo* ei ) {
    NodeSet::const_iterator mem_it = ei->d_mem.begin();
    Node mem_rep = getRepresentative( new_mem_exp[0] );
    Node new_mem_rel = new_mem_exp[1];
    Node new_mem_fst = RelsUtils::nthElementOfTuple( new_mem_exp[0], 0 );
    Node new_mem_snd = RelsUtils::nthElementOfTuple( new_mem_exp[0], 1 );
    for( ; mem_it != ei->d_mem.end(); mem_it++ ) {
      if( *mem_it == mem_rep ) {
        continue;
      }
      Node d_mem_exp = (*ei->d_mem_exp.find(*mem_it)).second;
      Node d_mem_fst = RelsUtils::nthElementOfTuple( d_mem_exp[0], 0 );
      Node d_mem_snd = RelsUtils::nthElementOfTuple( d_mem_exp[0], 1 );
      Node d_mem_rel = d_mem_exp[1];
      if( areEqual( new_mem_fst, d_mem_snd) ) {
        Node reason = NodeManager::currentNM()->mkNode( kind::AND, new_mem_exp, d_mem_exp );
        reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, new_mem_fst, d_mem_snd ) );
        if( new_mem_rel != ei->d_tc.get() ) {
          reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, new_mem_rel, ei->d_tc.get() ) );
        }
        if( d_mem_rel != ei->d_tc.get() ) {
          reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, d_mem_rel, ei->d_tc.get() ) );
        }
        Node new_membership = NodeManager::currentNM()->mkNode( kind::MEMBER, RelsUtils::constructPair( d_mem_rel, d_mem_fst, new_mem_snd ), ei->d_tc.get() );
        sendMergeInfer( new_membership, reason, "TCLOSURE-UP II" );
      }
      if( areEqual( new_mem_snd, d_mem_fst ) ) {
        Node reason = NodeManager::currentNM()->mkNode( kind::AND, new_mem_exp, d_mem_exp );
        reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, new_mem_snd, d_mem_fst ) );
        if( new_mem_rel != ei->d_tc.get() ) {
          reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, new_mem_rel, ei->d_tc.get() ) );
        }
        if( d_mem_rel != ei->d_tc.get() ) {
          reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, d_mem_rel, ei->d_tc.get() ) );
        }
        Node new_membership = NodeManager::currentNM()->mkNode( kind::MEMBER, RelsUtils::constructPair( d_mem_rel, new_mem_fst, d_mem_snd ), ei->d_tc.get() );
        sendMergeInfer( new_membership, reason, "TCLOSURE-UP II" );
      }
    }
  }


  void TheorySetsRels::doPendingMerge() {
    for( NodeList::const_iterator itr = d_pending_merge.begin(); itr != d_pending_merge.end(); itr++ ) {
      if( !holds(*itr) ) {
        if( d_lemmas_produced.find(*itr)==d_lemmas_produced.end() ) {
          Trace("rels-std-lemma") << "[std-sets-rels-lemma] Send out a merge fact as lemma: "
                              << *itr << std::endl;
          d_sets_theory.d_out->lemma( *itr );
          d_lemmas_produced.insert(*itr);
        }
      }
    }
  }

  // t1 and t2 can be both relations
  // or t1 is a tuple, t2 is a transposed relation
  void TheorySetsRels::sendInferTranspose( Node t1, Node t2, Node exp ) {
    Assert( t2.getKind() == kind::TRANSPOSE );

    if( isRel(t1) && isRel(t2) ) {
      Assert(t1.getKind() == kind::TRANSPOSE);
      sendMergeInfer(NodeManager::currentNM()->mkNode(kind::EQUAL, t1[0], t2[0]), exp, "Transpose-Equal");
      return;
    }
    sendMergeInfer(NodeManager::currentNM()->mkNode(kind::MEMBER, RelsUtils::reverseTuple(t1), t2[0]), exp, "Transpose-Rule");
  }

  void TheorySetsRels::sendMergeInfer( Node fact, Node reason, const char * c ) {
    if( !holds( fact ) ) {
      Node lemma = NodeManager::currentNM()->mkNode( kind::IMPLIES, reason, fact);
      d_pending_merge.push_back(lemma);
      Trace("rels-std") << "[std-rels-lemma] Generate a lemma by applying " << c
                        << ": " << lemma << std::endl;
    }
  }

  void TheorySetsRels::sendInferProduct( Node member, Node pt_rel, Node exp ) {
    Assert( pt_rel.getKind() == kind::PRODUCT );

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

}
}
}
