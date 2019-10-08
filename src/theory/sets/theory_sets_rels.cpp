/*********************                                                        */
/*! \file theory_sets_rels.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

typedef std::map< Node, std::vector< Node > >::iterator                                         MEM_IT;
typedef std::map< kind::Kind_t, std::vector< Node > >::iterator                                 KIND_TERM_IT;
typedef std::map< Node, std::unordered_set< Node, NodeHashFunction > >::iterator                     TC_GRAPH_IT;
typedef std::map< Node, std::map< kind::Kind_t, std::vector< Node > > >::iterator               TERM_IT;
typedef std::map< Node, std::map< Node, std::unordered_set< Node, NodeHashFunction > > >::iterator   TC_IT;

TheorySetsRels::TheorySetsRels(SolverState& s,
                               InferenceManager& im,
                               eq::EqualityEngine& e,
                               context::UserContext* u)
    : d_state(s), d_im(im), d_ee(e), d_shared_terms(u)
{
  d_trueNode = NodeManager::currentNM()->mkConst(true);
  d_falseNode = NodeManager::currentNM()->mkConst(false);
  d_ee.addFunctionKind(PRODUCT);
  d_ee.addFunctionKind(JOIN);
  d_ee.addFunctionKind(TRANSPOSE);
  d_ee.addFunctionKind(TCLOSURE);
  d_ee.addFunctionKind(JOIN_IMAGE);
  d_ee.addFunctionKind(IDEN);
  d_ee.addFunctionKind(APPLY_CONSTRUCTOR);
}

TheorySetsRels::~TheorySetsRels() {}

void TheorySetsRels::check(Theory::Effort level)
{
  Trace("rels") << "\n[sets-rels] ******************************* Start the "
                   "relational solver, effort = "
                << level << " *******************************\n"
                << std::endl;
  if (Theory::fullEffort(level))
  {
    collectRelsInfo();
    check();
    doPendingInfers();
  }
  Assert(d_pending.empty());
  Trace("rels") << "\n[sets-rels] ******************************* Done with "
                   "the relational solver *******************************\n"
                << std::endl;
}

  void TheorySetsRels::check() {
    MEM_IT m_it = d_rReps_memberReps_cache.begin();

    while(m_it != d_rReps_memberReps_cache.end()) {
      Node rel_rep = m_it->first;

      for(unsigned int i = 0; i < m_it->second.size(); i++) {
        Node    mem     = d_rReps_memberReps_cache[rel_rep][i];
        Node    exp     = d_rReps_memberReps_exp_cache[rel_rep][i];
        std::map<kind::Kind_t, std::vector<Node> >& kind_terms =
            d_terms_cache[rel_rep];

        if( kind_terms.find(kind::TRANSPOSE) != kind_terms.end() ) {
          std::vector<Node>& tp_terms = kind_terms[TRANSPOSE];
          if( tp_terms.size() > 0 ) {
            applyTransposeRule( tp_terms );
            applyTransposeRule( tp_terms[0], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::JOIN) != kind_terms.end() ) {
          std::vector<Node>& join_terms = kind_terms[JOIN];
          for( unsigned int j = 0; j < join_terms.size(); j++ ) {
            applyJoinRule( join_terms[j], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::PRODUCT) != kind_terms.end() ) {
          std::vector<Node>& product_terms = kind_terms[PRODUCT];
          for( unsigned int j = 0; j < product_terms.size(); j++ ) {
            applyProductRule( product_terms[j], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::TCLOSURE) != kind_terms.end() ) {
          std::vector<Node>& tc_terms = kind_terms[TCLOSURE];
          for( unsigned int j = 0; j < tc_terms.size(); j++ ) {
            applyTCRule( mem, tc_terms[j], rel_rep, exp );
          }
        }
        if( kind_terms.find(kind::JOIN_IMAGE) != kind_terms.end() ) {
          std::vector<Node>& join_image_terms = kind_terms[JOIN_IMAGE];
          for( unsigned int j = 0; j < join_image_terms.size(); j++ ) {
            applyJoinImageRule( mem, join_image_terms[j], exp );
          }
        }
        if( kind_terms.find(kind::IDEN) != kind_terms.end() ) {
          std::vector<Node>& iden_terms = kind_terms[IDEN];
          for( unsigned int j = 0; j < iden_terms.size(); j++ ) {
            applyIdenRule( mem, iden_terms[j], exp );
          }
        }
      }
      ++m_it;
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
              ++term_it;
            }
          } else if( k_t_it->first == kind::TRANSPOSE ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              computeMembersForUnaryOpRel( *term_it );
              ++term_it;
            }
          } else if ( k_t_it->first == kind::TCLOSURE ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              buildTCGraphForRel( *term_it );
              ++term_it;
            }
          } else if( k_t_it->first == kind::JOIN_IMAGE ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              computeMembersForJoinImageTerm( *term_it );
              ++term_it;
            }
          } else if( k_t_it->first == kind::IDEN ) {
            std::vector<Node>::iterator term_it = k_t_it->second.begin();
            while( term_it != k_t_it->second.end() ) {
              computeMembersForIdenTerm( *term_it );
              ++term_it;
            }
          }
          ++k_t_it;
        }
      }
      ++t_it;
    }
    doTCInference();

    // clean up
    d_tuple_reps.clear();
    d_rReps_memberReps_exp_cache.clear();
    d_terms_cache.clear();
    d_membership_trie.clear();
    d_rel_nodes.clear();
    d_rReps_memberReps_cache.clear();
    d_rRep_tcGraph.clear();
    d_tcr_tcGraph_exps.clear();
    d_tcr_tcGraph.clear();
  }

  /*
   * Populate relational terms data structure
   */

  void TheorySetsRels::collectRelsInfo() {
    Trace("rels") << "[sets-rels] Start collecting relational terms..." << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(&d_ee);
    while( !eqcs_i.isFinished() ){
      Node                      eqc_rep  = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc_rep, &d_ee);

      TypeNode erType = eqc_rep.getType();
      Trace("rels-ee") << "[sets-rels-ee] Eqc term representative: " << eqc_rep << " with type " << eqc_rep.getType() << std::endl;

      while( !eqc_i.isFinished() ){
        Node eqc_node = (*eqc_i);

        Trace("rels-ee") << "  term : " << eqc_node << std::endl;

        if (erType.isBoolean() && eqc_rep.isConst())
        {
          // collect membership info
          if( eqc_node.getKind() == kind::MEMBER && eqc_node[1].getType().getSetElementType().isTuple()) {
            Node tup_rep = getRepresentative( eqc_node[0] );
            Node rel_rep = getRepresentative( eqc_node[1] );

            if( eqc_node[0].isVar() ){
              reduceTupleVar( eqc_node );
            }

            bool is_true_eq = eqc_rep.getConst<bool>();
            Node reason        = is_true_eq ? eqc_node : eqc_node.negate();

            if( is_true_eq ) {
              if( safelyAddToMap(d_rReps_memberReps_cache, rel_rep, tup_rep) ) {
                d_rReps_memberReps_exp_cache[rel_rep].push_back(reason);
                computeTupleReps(tup_rep);
                d_membership_trie[rel_rep].addTerm(tup_rep, d_tuple_reps[tup_rep]);
              }
            }
          }
        // collect relational terms info
        }
        else if (erType.isSet() && erType.getSetElementType().isTuple())
        {
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
        }
        else if (erType.isTuple() && !eqc_node.isConst() && !eqc_node.isVar())
        {
          for (unsigned i = 0, tlen = erType.getTupleLength(); i < tlen; i++)
          {
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
    NodeManager* nm = NodeManager::currentNM();

    Node join_image_rel = join_image_term[0];
    std::unordered_set< Node, NodeHashFunction > hasChecked;
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
      if (d_state.isEntailed(new_membership, true))
      {
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
              sendInfer(
                  new_membership,
                  reasons.size() > 1 ? nm->mkNode(AND, reasons) : reasons[0],
                  "JOIN-IMAGE UP");
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
    sendInfer(conclusion, reason, "JOIN-IMAGE DOWN");
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
    NodeManager* nm = NodeManager::currentNM();
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
    sendInfer(nm->mkNode(AND, fact, nm->mkNode(EQUAL, fst_mem, snd_mem)),
              reason,
              "IDENTITY-DOWN");
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
    NodeManager* nm = NodeManager::currentNM();

    MEM_IT rel_mem_exp_it = d_rReps_memberReps_exp_cache.find( iden_term_rel_rep );
    std::vector< Node >::iterator mem_rep_exp_it = (*rel_mem_exp_it).second.begin();

    while( mem_rep_exp_it != (*rel_mem_exp_it).second.end() ) {
      Node reason = *mem_rep_exp_it;
      Node fst_exp_mem = RelsUtils::nthElementOfTuple( (*mem_rep_exp_it)[0], 0 );
      Node new_mem = RelsUtils::constructPair( iden_term, fst_exp_mem, fst_exp_mem );

      if( (*mem_rep_exp_it)[1] != iden_term_rel ) {
        reason = NodeManager::currentNM()->mkNode( kind::AND, reason, NodeManager::currentNM()->mkNode( kind::EQUAL, (*mem_rep_exp_it)[1], iden_term_rel ) );
      }
      sendInfer(nm->mkNode(MEMBER, new_mem, iden_term), reason, "IDENTITY-UP");
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
        std::unordered_set< Node, NodeHashFunction > sets;
        sets.insert( mem_rep_snd );
        (tc_it->second)[mem_rep_fst] = sets;
      }
    } else {
      std::map< Node, Node > exp_map;
      std::unordered_set< Node, NodeHashFunction > sets;
      std::map< Node, std::unordered_set<Node, NodeHashFunction> > element_map;
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
    d_pending.push_back(tc_lemma);
  }

  bool TheorySetsRels::isTCReachable( Node mem_rep, Node tc_rel ) {
    MEM_IT mem_it = d_rReps_memberReps_cache.find( getRepresentative( tc_rel[0] ) );

    if( mem_it != d_rReps_memberReps_cache.end() && std::find( (mem_it->second).begin(), (mem_it->second).end(), mem_rep) != (mem_it->second).end() ) {
      return true;
    }

    TC_IT tc_it = d_rRep_tcGraph.find( getRepresentative(tc_rel[0]) );
    if( tc_it != d_rRep_tcGraph.end() ) {
      bool isReachable = false;
      std::unordered_set<Node, NodeHashFunction> seen;
      isTCReachable( getRepresentative( RelsUtils::nthElementOfTuple(mem_rep, 0) ),
                     getRepresentative( RelsUtils::nthElementOfTuple(mem_rep, 1) ), seen, tc_it->second, isReachable );
      return isReachable;
    }
    return false;
  }

  void TheorySetsRels::isTCReachable( Node start, Node dest, std::unordered_set<Node, NodeHashFunction>& hasSeen,
                                    std::map< Node, std::unordered_set< Node, NodeHashFunction > >& tc_graph, bool& isReachable ) {
    if(hasSeen.find(start) == hasSeen.end()) {
      hasSeen.insert(start);
    }

    TC_GRAPH_IT pair_set_it = tc_graph.find(start);

    if(pair_set_it != tc_graph.end()) {
      if(pair_set_it->second.find(dest) != pair_set_it->second.end()) {
        isReachable = true;
        return;
      } else {
        std::unordered_set< Node, NodeHashFunction >::iterator set_it = pair_set_it->second.begin();

        while( set_it != pair_set_it->second.end() ) {
          // need to check if *set_it has been looked already
          if( hasSeen.find(*set_it) == hasSeen.end() ) {
            isTCReachable( *set_it, dest, hasSeen, tc_graph, isReachable );
          }
          ++set_it;
        }
      }
    }
  }

  void TheorySetsRels::buildTCGraphForRel( Node tc_rel ) {
    std::map< Node, Node > rel_tc_graph_exps;
    std::map< Node, std::unordered_set<Node, NodeHashFunction> > rel_tc_graph;

    Node rel_rep = getRepresentative( tc_rel[0] );
    Node tc_rel_rep = getRepresentative( tc_rel );
    std::vector< Node > members = d_rReps_memberReps_cache[rel_rep];
    std::vector< Node > exps = d_rReps_memberReps_exp_cache[rel_rep];

    for( unsigned int i = 0; i < members.size(); i++ ) {
      Node fst_element_rep = getRepresentative( RelsUtils::nthElementOfTuple( members[i], 0 ));
      Node snd_element_rep = getRepresentative( RelsUtils::nthElementOfTuple( members[i], 1 ));
      Node tuple_rep = RelsUtils::constructPair( rel_rep, fst_element_rep, snd_element_rep );
      std::map< Node, std::unordered_set<Node, NodeHashFunction> >::iterator rel_tc_graph_it = rel_tc_graph.find( fst_element_rep );

      if( rel_tc_graph_it == rel_tc_graph.end() ) {
        std::unordered_set< Node, NodeHashFunction > snd_elements;
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

  void TheorySetsRels::doTCInference( std::map< Node, std::unordered_set<Node, NodeHashFunction> > rel_tc_graph, std::map< Node, Node > rel_tc_graph_exps, Node tc_rel ) {
    Trace("rels-debug") << "[Theory::Rels] ****** doTCInference !" << std::endl;
    for (TC_GRAPH_IT tc_graph_it = rel_tc_graph.begin();
         tc_graph_it != rel_tc_graph.end();
         ++tc_graph_it)
    {
      for (std::unordered_set<Node, NodeHashFunction>::iterator
               snd_elements_it = tc_graph_it->second.begin();
           snd_elements_it != tc_graph_it->second.end();
           ++snd_elements_it)
      {
        std::vector< Node > reasons;
        std::unordered_set<Node, NodeHashFunction> seen;
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

  void TheorySetsRels::doTCInference(Node tc_rel, std::vector< Node > reasons, std::map< Node, std::unordered_set< Node, NodeHashFunction > >& tc_graph,
                                       std::map< Node, Node >& rel_tc_graph_exps, Node start_node_rep, Node cur_node_rep, std::unordered_set< Node, NodeHashFunction >& seen ) {
    NodeManager* nm = NodeManager::currentNM();
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
      sendInfer(nm->mkNode(MEMBER, tc_mem, tc_rel),
                nm->mkNode(AND, all_reasons),
                "TCLOSURE-Forward");
    } else {
      sendInfer(nm->mkNode(MEMBER, tc_mem, tc_rel),
                all_reasons.front(),
                "TCLOSURE-Forward");
    }

    // check if cur_node has been traversed or not
    if( seen.find( cur_node_rep ) != seen.end() ) {
      return;
    }
    seen.insert( cur_node_rep );
    TC_GRAPH_IT  cur_set = tc_graph.find( cur_node_rep );
    if( cur_set != tc_graph.end() ) {
      for (std::unordered_set<Node, NodeHashFunction>::iterator set_it =
               cur_set->second.begin();
           set_it != cur_set->second.end();
           ++set_it)
      {
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
    sendInfer(fact_1, reason, "product-split");
    sendInfer(fact_2, reason, "product-split");
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
    Node shared_x = d_state.getSkolemCache().mkTypedSkolemCached(
        shared_type, mem, join_rel, SkolemCache::SK_JOIN, "srj");
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
    sendInfer(fact, reason, "JOIN-Split-1");
    fact = NodeManager::currentNM()->mkNode(kind::MEMBER, mem2, join_rel[1]);
    sendInfer(fact, reason, "JOIN-Split-2");
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
    NodeManager* nm = NodeManager::currentNM();
    for( unsigned int i = 1; i < tp_terms.size(); i++ ) {
      Trace("rels-debug") << "\n[Theory::Rels] *********** Applying TRANSPOSE-Equal rule on transposed term = " << tp_terms[0] << " and " << tp_terms[i] << std::endl;
      sendInfer(nm->mkNode(EQUAL, tp_terms[0][0], tp_terms[i][0]),
                nm->mkNode(EQUAL, tp_terms[0], tp_terms[i]),
                "TRANSPOSE-Equal");
    }
  }

  void TheorySetsRels::applyTransposeRule( Node tp_rel, Node tp_rel_rep, Node exp ) {
    Trace("rels-debug") << "\n[Theory::Rels] *********** Applying TRANSPOSE rule on transposed term = " << tp_rel
                        << ", its representative = " << tp_rel_rep
                        << " with explanation = " << exp << std::endl;
    NodeManager* nm = NodeManager::currentNM();

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
    sendInfer(nm->mkNode(MEMBER, reversed_mem, tp_rel[0]),
              reason,
              "TRANSPOSE-Reverse");
  }

  void TheorySetsRels::doTCInference() {
    Trace("rels-debug") << "[Theory::Rels] ****** Finalizing transitive closure inferences!" << std::endl;
    TC_IT tc_graph_it = d_tcr_tcGraph.begin();
    while( tc_graph_it != d_tcr_tcGraph.end() ) {
      Assert ( d_tcr_tcGraph_exps.find(tc_graph_it->first) != d_tcr_tcGraph_exps.end() );
      doTCInference( tc_graph_it->second, d_tcr_tcGraph_exps.find(tc_graph_it->first)->second, tc_graph_it->first );
      ++tc_graph_it;
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
    if (d_rReps_memberReps_cache.find(rel0_rep)
        == d_rReps_memberReps_cache.end())
    {
      return;
    }
    NodeManager* nm = NodeManager::currentNM();

    std::vector<Node>   members = d_rReps_memberReps_cache[rel0_rep];
    std::vector<Node>   exps    = d_rReps_memberReps_exp_cache[rel0_rep];

    Assert( members.size() == exps.size() );

    for(unsigned int i = 0; i < members.size(); i++) {
      Node reason = exps[i];
      if( rel.getKind() == kind::TRANSPOSE) {
        if( rel[0] != exps[i][1] ) {
          reason = NodeManager::currentNM()->mkNode(kind::AND, reason, NodeManager::currentNM()->mkNode(kind::EQUAL, rel[0], exps[i][1]));
        }
        sendInfer(nm->mkNode(MEMBER, RelsUtils::reverseTuple(exps[i][0]), rel),
                  reason,
                  "TRANSPOSE-reverse");
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
    NodeManager* nm = NodeManager::currentNM();

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
            sendInfer(fact,
                      nm->mkNode(kind::AND, reasons),
                      "PRODUCT-Compose");
          } else {
            if( r1_rmost != r2_lmost ) {
              reasons.push_back( NodeManager::currentNM()->mkNode(kind::EQUAL, r1_rmost, r2_lmost) );
            }
            sendInfer(fact, nm->mkNode(kind::AND, reasons), "JOIN-Compose");
          }
        }
      }
    }

  }

  void TheorySetsRels::doPendingInfers()
  {
    // process the inferences in d_pending
    if (!d_state.isInConflict())
    {
      for (const Node& p : d_pending)
      {
        if (p.getKind() == IMPLIES)
        {
          processInference(p[1], p[0], "rels");
        }
        else
        {
          processInference(p, d_trueNode, "rels");
        }
        if (d_state.isInConflict())
        {
          break;
        }
      }
      // if we are still not in conflict, send lemmas
      if (!d_state.isInConflict())
      {
        d_im.flushPendingLemmas();
      }
    }
    d_pending.clear();
  }

  void TheorySetsRels::processInference(Node conc, Node exp, const char* c)
  {
    Trace("sets-pinfer") << "Process inference: " << exp << " => " << conc
                         << std::endl;
    if (!d_state.isEntailed(exp, true))
    {
      Trace("sets-pinfer") << "  must assert as lemma" << std::endl;
      // we wrap the spurious explanation into a splitting lemma
      Node lem = NodeManager::currentNM()->mkNode(OR, exp.negate(), conc);
      d_im.assertInference(lem, d_trueNode, c, 1);
      return;
    }
    // try to assert it as a fact
    d_im.assertInference(conc, exp, c);
  }

  bool TheorySetsRels::isRelationKind( Kind k ) {
    return k == TRANSPOSE || k == PRODUCT || k == JOIN || k == TCLOSURE
           || k == IDEN || k == JOIN_IMAGE;
  }

  Node TheorySetsRels::getRepresentative( Node t ) {
    if (d_ee.hasTerm(t))
    {
      return d_ee.getRepresentative(t);
    }
    else
    {
      return t;
    }
  }

  bool TheorySetsRels::hasTerm(Node a) { return d_ee.hasTerm(a); }
  bool TheorySetsRels::areEqual( Node a, Node b ){
    Assert(a.getType() == b.getType());
    Trace("rels-eq") << "[sets-rels]**** checking equality between " << a << " and " << b << std::endl;
    if(a == b) {
      return true;
    } else if( hasTerm( a ) && hasTerm( b ) ){
      return d_ee.areEqual(a, b);
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
        ++mems;
      }
      map[rel_rep].push_back(member);
      return true;
    }
    return false;
  }

  void TheorySetsRels::makeSharedTerm( Node n ) {
    if(d_shared_terms.find(n) == d_shared_terms.end()) {
      Trace("rels-share") << " [sets-rels] making shared term " << n
                          << std::endl;
      Node skolem = NodeManager::currentNM()->mkSkolem( "sts", NodeManager::currentNM()->mkSetType( n.getType() ) );
      Node skEq =
          skolem.eqNode(NodeManager::currentNM()->mkNode(kind::SINGLETON, n));
      // force lemma to be sent immediately
      d_im.assertInference(skEq, d_trueNode, "shared-term");
      d_im.flushPendingLemmas();
      d_shared_terms.insert(n);
    }
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
      sendInfer(tuple_reduction_lemma, d_trueNode, "tuple-reduction");
      d_symbolic_tuples.insert(n);
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
          ++it;
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
        ++it;
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

  void TheorySetsRels::sendInfer(Node fact, Node reason, const char* c)
  {
    Trace("rels-lemma") << "Rels::lemma " << fact << " from " << reason
                        << " by " << c << std::endl;
    Node lemma = NodeManager::currentNM()->mkNode(IMPLIES, reason, fact);
    d_pending.push_back(lemma);
  }
}
}
}
