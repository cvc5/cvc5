/*********************                                                        */
/*! \file theory_sep.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of sep.
 **
 ** Implementation of the theory of sep.
 **/


#include "theory/sep/theory_sep.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include <map>
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "options/sep_options.h"
#include "options/smt_options.h"
#include "smt/logic_exception.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/term_database.h"
#include "options/quantifiers_options.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace sep {

TheorySep::TheorySep(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_SEP, c, u, out, valuation, logicInfo),
  d_lemmas_produced_c(u),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sep::TheorySep", true),
  d_conflict(c, false),
  d_reduce(u),
  d_infer(c),
  d_infer_exp(c),
  d_spatial_assertions(c)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
  d_bounds_init = false;
  
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::SEP_PTO);
  //d_equalityEngine.addFunctionKind(kind::SEP_STAR);
}

TheorySep::~TheorySep() {
  for( std::map< Node, HeapAssertInfo * >::iterator it = d_eqc_info.begin(); it != d_eqc_info.end(); ++it ){
    delete it->second;
  }
}

void TheorySep::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

Node TheorySep::mkAnd( std::vector< TNode >& assumptions ) {
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////



Node TheorySep::ppRewrite(TNode term) {
  Trace("sep-pp") << "ppRewrite : " << term << std::endl;
  return term;
}

Theory::PPAssertStatus TheorySep::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {

  return PP_ASSERT_STATUS_UNSOLVED;
}


/////////////////////////////////////////////////////////////////////////////
// T-PROPAGATION / REGISTRATION
/////////////////////////////////////////////////////////////////////////////


bool TheorySep::propagate(TNode literal)
{
  Debug("sep") << "TheorySep::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("sep") << "TheorySep::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}/* TheorySep::propagate(TNode) */


void TheorySep::explain(TNode literal, std::vector<TNode>& assumptions) {
  if( literal.getKind()==kind::SEP_LABEL ||
      ( literal.getKind()==kind::NOT && literal[0].getKind()==kind::SEP_LABEL ) ){
    //labelled assertions are never given to equality engine and should only come from the outside
    assumptions.push_back( literal );
  }else{
    // Do the work
    bool polarity = literal.getKind() != kind::NOT;
    TNode atom = polarity ? literal : literal[0];
    if (atom.getKind() == kind::EQUAL) {
      d_equalityEngine.explainEquality( atom[0], atom[1], polarity, assumptions, NULL );
    } else {
      d_equalityEngine.explainPredicate( atom, polarity, assumptions );
    }
  }
}


void TheorySep::propagate(Effort e){

}


Node TheorySep::explain(TNode literal)
{
  Debug("sep") << "TheorySep::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}


/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////


void TheorySep::addSharedTerm(TNode t) {
  Debug("sep") << "TheorySep::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_SEP);
}


EqualityStatus TheorySep::getEqualityStatus(TNode a, TNode b) {
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  else if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_UNKNOWN;//FALSE_IN_MODEL;
}


void TheorySep::computeCareGraph() {
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
        // If we know about it, we should have propagated it, so we can skip
        break;
      default:
        // Let's split on it
        addCarePair(a, b);
        break;
      }
    }
  }
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheorySep::collectModelInfo( TheoryModel* m, bool fullModel ){
  set<Node> termSet;

  // Compute terms appearing in assertions and shared terms
  computeRelevantTerms(termSet);

  // Send the equality engine information to the model
  m->assertEqualityEngine( &d_equalityEngine, &termSet );
}

void TheorySep::postProcessModel( TheoryModel* m ){
  Trace("sep-model") << "Printing model for TheorySep..." << std::endl;
  
  std::vector< Node > sep_children;
  Node m_neq;
  Node m_heap;
  for( std::map< TypeNode, Node >::iterator it = d_base_label.begin(); it != d_base_label.end(); ++it ){
    //should only be constructing for one heap type
    Assert( m_heap.isNull() );
    Assert( d_loc_to_data_type.find( it->first )!=d_loc_to_data_type.end() );
    Trace("sep-model") << "Model for heap, type = " << it->first << " with data type " << d_loc_to_data_type[it->first] << " : " << std::endl;
    TypeNode data_type = d_loc_to_data_type[it->first];
    computeLabelModel( it->second );
    if( d_label_model[it->second].d_heap_locs_model.empty() ){
      Trace("sep-model") << "  [empty]" << std::endl;
    }else{
      for( unsigned j=0; j<d_label_model[it->second].d_heap_locs_model.size(); j++ ){
        Assert( d_label_model[it->second].d_heap_locs_model[j].getKind()==kind::SINGLETON );
        std::vector< Node > pto_children;
        Node l = d_label_model[it->second].d_heap_locs_model[j][0];
        Assert( l.isConst() );
        pto_children.push_back( l );
        Trace("sep-model") << " " << l << " -> ";
        if( d_pto_model[l].isNull() ){
          Trace("sep-model") << "_";
          //m->d_comment_str << "_";
          TypeEnumerator te_range( data_type );
          if( data_type.isInterpretedFinite() ){
            pto_children.push_back( *te_range );
          }else{
            //must enumerate until we find one that is not explicitly pointed to
            bool success = false;
            Node cv;
            do{
              cv = *te_range;
              if( std::find( d_heap_locs_nptos[l].begin(), d_heap_locs_nptos[l].end(), cv )==d_heap_locs_nptos[l].end() ){
                success = true;
              }else{
                ++te_range;
              }
            }while( !success );
            pto_children.push_back( cv );
          }
        }else{
          Trace("sep-model") << d_pto_model[l];
          Node vpto = d_valuation.getModel()->getRepresentative( d_pto_model[l] );
          Assert( vpto.isConst() );
          pto_children.push_back( vpto );
        }
        Trace("sep-model") << std::endl;
        sep_children.push_back( NodeManager::currentNM()->mkNode( kind::SEP_PTO, pto_children ) );
      }
    }
    Node nil = getNilRef( it->first );
    Node vnil = d_valuation.getModel()->getRepresentative( nil );
    m_neq = NodeManager::currentNM()->mkNode( kind::EQUAL, nil, vnil );
    Trace("sep-model") << "sep.nil = " << vnil << std::endl;
    Trace("sep-model") << std::endl;
    if( sep_children.empty() ){
      TypeEnumerator te_domain( it->first );
      TypeEnumerator te_range( d_loc_to_data_type[it->first] );
      m_heap = NodeManager::currentNM()->mkNode( kind::SEP_EMP, *te_domain, *te_range );
    }else if( sep_children.size()==1 ){
      m_heap = sep_children[0];
    }else{
      m_heap = NodeManager::currentNM()->mkNode( kind::SEP_STAR, sep_children );
    }
    m->setHeapModel( m_heap, m_neq );
  }
  Trace("sep-model") << "Finished printing model for TheorySep." << std::endl;
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheorySep::presolve() {
  Trace("sep-pp") << "Presolving" << std::endl;
  //TODO: cleanup if incremental?
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


void TheorySep::check(Effort e) {
  if (done() && !fullEffort(e) && e != EFFORT_LAST_CALL) {
    return;
  }

  getOutputChannel().spendResource(options::theoryCheckStep());

  TimerStat::CodeTimer checkTimer(d_checkTime);
  Trace("sep-check") << "Sep::check(): " << e << endl;

  while( !done() && !d_conflict ){
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("sep-assert") << "TheorySep::check(): processing " << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];
    /*
    if( atom.getKind()==kind::SEP_EMP ){
      TypeNode tn = atom[0].getType();
      if( d_emp_arg.find( tn )==d_emp_arg.end() ){
        d_emp_arg[tn] = atom[0];
      }else{
        //normalize argument TODO
      }
    }
    */
    TNode s_atom = atom.getKind()==kind::SEP_LABEL ? atom[0] : atom;
    TNode s_lbl = atom.getKind()==kind::SEP_LABEL ? atom[1] : TNode::null();
    bool is_spatial = s_atom.getKind()==kind::SEP_STAR || s_atom.getKind()==kind::SEP_WAND || s_atom.getKind()==kind::SEP_PTO || s_atom.getKind()==kind::SEP_EMP;
    if( is_spatial && s_lbl.isNull() ){
      if( d_reduce.find( fact )==d_reduce.end() ){
        Trace("sep-lemma-debug") << "Reducing unlabelled assertion " << atom << std::endl;
        d_reduce.insert( fact );
        //introduce top-level label, add iff
        TypeNode refType = getReferenceType( s_atom );
        Trace("sep-lemma-debug") << "...reference type is : " << refType << std::endl;
        Node b_lbl = getBaseLabel( refType );
        Node s_atom_new = NodeManager::currentNM()->mkNode( kind::SEP_LABEL, s_atom, b_lbl );
        Node lem;
        Trace("sep-lemma-debug") << "...polarity is " << polarity << std::endl;
        if( polarity ){
          lem = NodeManager::currentNM()->mkNode( kind::OR, s_atom.negate(), s_atom_new );
        }else{
          lem = NodeManager::currentNM()->mkNode( kind::OR, s_atom, s_atom_new.negate() );
        }
        Trace("sep-lemma-debug") << "Sep::Lemma : base reduction : " << lem << std::endl;
        d_out->lemma( lem );
      }
    }else{
      //do reductions
      if( is_spatial ){
        if( d_reduce.find( fact )==d_reduce.end() ){
          Trace("sep-lemma-debug") << "Reducing assertion " << fact << std::endl;
          d_reduce.insert( fact );
          Node conc;
          std::map< Node, Node >::iterator its = d_red_conc[s_lbl].find( s_atom );
          if( its==d_red_conc[s_lbl].end() ){
            //make conclusion based on type of assertion
            if( s_atom.getKind()==kind::SEP_STAR || s_atom.getKind()==kind::SEP_WAND ){
              std::vector< Node > children;
              std::vector< Node > c_lems;
              TypeNode tn = getReferenceType( s_atom );
              if( d_reference_bound_max.find( tn )!=d_reference_bound_max.end() ){
                c_lems.push_back( NodeManager::currentNM()->mkNode( kind::SUBSET, s_lbl, d_reference_bound_max[tn] ) );
              }
              std::vector< Node > labels;
              getLabelChildren( s_atom, s_lbl, children, labels );
              Node empSet = NodeManager::currentNM()->mkConst(EmptySet(s_lbl.getType().toType()));
              Assert( children.size()>1 );
              if( s_atom.getKind()==kind::SEP_STAR ){
                //reduction for heap : union, pairwise disjoint
                Node ulem = NodeManager::currentNM()->mkNode( kind::UNION, labels[0], labels[1] );
                for( unsigned i=2; i<labels.size(); i++ ){
                  ulem = NodeManager::currentNM()->mkNode( kind::UNION, ulem, labels[i] );
                }
                ulem = s_lbl.eqNode( ulem );
                Trace("sep-lemma-debug") << "Sep::Lemma : star reduction, union : " << ulem << std::endl;
                c_lems.push_back( ulem );
                for( unsigned i=0; i<labels.size(); i++ ){
                  for( unsigned j=(i+1); j<labels.size(); j++ ){
                    Node s = NodeManager::currentNM()->mkNode( kind::INTERSECTION, labels[i], labels[j] );
                    Node ilem = s.eqNode( empSet );
                    Trace("sep-lemma-debug") << "Sep::Lemma : star reduction, disjoint : " << ilem << std::endl;
                    c_lems.push_back( ilem );
                  }
                }
              }else{
                Node ulem = NodeManager::currentNM()->mkNode( kind::UNION, s_lbl, labels[0] );
                ulem = ulem.eqNode( labels[1] );
                Trace("sep-lemma-debug") << "Sep::Lemma : wand reduction, union : " << ulem << std::endl;
                c_lems.push_back( ulem );
                Node s = NodeManager::currentNM()->mkNode( kind::INTERSECTION, s_lbl, labels[0] );
                Node ilem = s.eqNode( empSet );
                Trace("sep-lemma-debug") << "Sep::Lemma : wand reduction, disjoint : " << ilem << std::endl;
                c_lems.push_back( ilem );
                //nil does not occur in labels[0]
                Node nr = getNilRef( tn );
                Node nrlem = NodeManager::currentNM()->mkNode( kind::MEMBER, nr, labels[0] ).negate();
                Trace("sep-lemma") << "Sep::Lemma: sep.nil not in wand antecedant heap : " << nrlem << std::endl;
                d_out->lemma( nrlem );
              }
              //send out definitional lemmas for introduced sets
              for( unsigned j=0; j<c_lems.size(); j++ ){
                Trace("sep-lemma") << "Sep::Lemma : definition : " << c_lems[j] << std::endl;
                d_out->lemma( c_lems[j] );
              }
              //children.insert( children.end(), c_lems.begin(), c_lems.end() );
              conc = NodeManager::currentNM()->mkNode( kind::AND, children );
            }else if( s_atom.getKind()==kind::SEP_PTO ){
              Node ss = NodeManager::currentNM()->mkNode( kind::SINGLETON, s_atom[0] );
              if( s_lbl!=ss ){
                conc = s_lbl.eqNode( ss );
              }
              //not needed anymore: semantics of sep.nil is enforced globally
              //Node ssn = NodeManager::currentNM()->mkNode( kind::EQUAL, s_atom[0], getNilRef(s_atom[0].getType()) ).negate();
              //conc = conc.isNull() ? ssn : NodeManager::currentNM()->mkNode( kind::AND, conc, ssn );
              
            }else if( s_atom.getKind()==kind::SEP_EMP ){
              //conc = s_lbl.eqNode( NodeManager::currentNM()->mkConst(EmptySet(s_lbl.getType().toType())) );
              Node lem;
              Node emp_s = NodeManager::currentNM()->mkConst(EmptySet(s_lbl.getType().toType()));
              if( polarity ){
                lem = NodeManager::currentNM()->mkNode( kind::OR, fact.negate(), s_lbl.eqNode( emp_s ) );
              }else{
                Node kl = NodeManager::currentNM()->mkSkolem( "loc", getReferenceType( s_atom ) );
                Node kd = NodeManager::currentNM()->mkSkolem( "data", getDataType( s_atom ) );
                Node econc = NodeManager::currentNM()->mkNode( kind::SEP_LABEL, 
                               NodeManager::currentNM()->mkNode( kind::SEP_STAR, NodeManager::currentNM()->mkNode( kind::SEP_PTO, kl, kd ), d_true ), s_lbl );
                //Node econc = NodeManager::currentNM()->mkNode( kind::AND, s_lbl.eqNode( emp_s ).negate(), 
                lem = NodeManager::currentNM()->mkNode( kind::OR, fact.negate(), econc );
              }
              Trace("sep-lemma") << "Sep::Lemma : emp : " << lem << std::endl;
              d_out->lemma( lem );

            }else{
              //labeled emp should be rewritten
              Assert( false );
            }
            d_red_conc[s_lbl][s_atom] = conc;
          }else{
            conc = its->second;
          }
          if( !conc.isNull() ){
            bool use_polarity = s_atom.getKind()==kind::SEP_WAND ? !polarity : polarity;
            if( !use_polarity ){
              // introduce guard, assert positive version
              Trace("sep-lemma-debug") << "Negated spatial constraint asserted to sep theory: " << fact << std::endl;
              Node lit = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
              lit = getValuation().ensureLiteral( lit );
              d_neg_guard[s_lbl][s_atom] = lit;
              Trace("sep-lemma-debug") << "Neg guard : " << s_lbl << " " << s_atom << " " << lit << std::endl;
              AlwaysAssert( !lit.isNull() );
              d_out->requirePhase( lit, true );
              d_neg_guards.push_back( lit );
              d_guard_to_assertion[lit] = s_atom;
              //Node lem = NodeManager::currentNM()->mkNode( kind::EQUAL, lit, conc );
              Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit.negate(), conc );
              Trace("sep-lemma") << "Sep::Lemma : (neg) reduction : " << lem << std::endl;
              d_out->lemma( lem );
            }else{
              //reduce based on implication
              Node lem = NodeManager::currentNM()->mkNode( kind::OR, fact.negate(), conc );
              Trace("sep-lemma") << "Sep::Lemma : reduction : " << lem << std::endl;
              d_out->lemma( lem );
            }
          }else{
            Trace("sep-lemma-debug") << "Trivial conclusion, do not add lemma." << std::endl;
          }
        }
      }
      //assert to equality engine
      if( !is_spatial ){
        Trace("sep-assert") << "Asserting " << atom << ", pol = " << polarity << " to EE..." << std::endl;
        if( s_atom.getKind()==kind::EQUAL ){
          d_equalityEngine.assertEquality(atom, polarity, fact);
        }else{
          d_equalityEngine.assertPredicate(atom, polarity, fact);
        }
        Trace("sep-assert") << "Done asserting " << atom << " to EE." << std::endl;
      }else if( s_atom.getKind()==kind::SEP_PTO ){
        Node pto_lbl = NodeManager::currentNM()->mkNode( kind::SINGLETON, s_atom[0] );
        Assert( s_lbl==pto_lbl );
        Trace("sep-assert") << "Asserting " << s_atom << std::endl;
        d_equalityEngine.assertPredicate(s_atom, polarity, fact);
        //associate the equivalence class of the lhs with this pto
        Node r = getRepresentative( s_lbl );
        HeapAssertInfo * ei = getOrMakeEqcInfo( r, true );
        addPto( ei, r, atom, polarity );
      }
      //maybe propagate
      doPendingFacts();
      //add to spatial assertions
      if( !d_conflict && is_spatial ){
        d_spatial_assertions.push_back( fact );
      }
    }
  }

  if( e == EFFORT_LAST_CALL && !d_conflict && !d_valuation.needCheck() ){
    Trace("sep-process") << "Checking heap at full effort..." << std::endl;
    d_label_model.clear();
    d_tmodel.clear();
    d_pto_model.clear();
    Trace("sep-process") << "---Locations---" << std::endl;
    std::map< Node, int > min_id;
    for( std::map< TypeNode, std::vector< Node > >::iterator itt = d_type_references_all.begin(); itt != d_type_references_all.end(); ++itt ){
      for( unsigned k=0; k<itt->second.size(); k++ ){
        Node t = itt->second[k];
        Trace("sep-process") << "  " << t << " = ";
        if( d_valuation.getModel()->hasTerm( t ) ){
          Node v = d_valuation.getModel()->getRepresentative( t );
          Trace("sep-process") << v << std::endl;
          //take minimal id
          std::map< Node, unsigned >::iterator itrc = d_type_ref_card_id.find( t );
          int tid = itrc==d_type_ref_card_id.end() ? -1 : (int)itrc->second;
          bool set_term_model;
          if( d_tmodel.find( v )==d_tmodel.end() ){
            set_term_model = true;
          }else{
            set_term_model = min_id[v]>tid;
          }
          if( set_term_model ){
            d_tmodel[v] = t;
            min_id[v] = tid;
          }
        }else{
          Trace("sep-process") << "?" << std::endl;
        }
      }
    }
    Trace("sep-process") << "---" << std::endl;
    //build positive/negative assertion lists for labels
    std::map< Node, bool > assert_active;
    //get the inactive assertions
    std::map< Node, std::vector< Node > > lbl_to_assertions;
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      bool polarity = fact.getKind() != kind::NOT;
      TNode atom = polarity ? fact : fact[0];
      Assert( atom.getKind()==kind::SEP_LABEL );
      TNode s_atom = atom[0];
      TNode s_lbl = atom[1];
      lbl_to_assertions[s_lbl].push_back( fact );
      //check whether assertion is active : either polarity=true, or guard is not asserted false
      assert_active[fact] = true;
      bool use_polarity = s_atom.getKind()==kind::SEP_WAND ? !polarity : polarity;
      if( use_polarity ){
        if( s_atom.getKind()==kind::SEP_PTO ){
          Node vv = d_valuation.getModel()->getRepresentative( s_atom[0] );
          if( d_pto_model.find( vv )==d_pto_model.end() ){
            Trace("sep-process") << "Pto : " << s_atom[0] << " (" << vv << ") -> " << s_atom[1] << std::endl;
            d_pto_model[vv] = s_atom[1];
            
            //replace this on pto-model since this term is more relevant
            TypeNode vtn = vv.getType();
            if( std::find( d_type_references_all[vtn].begin(), d_type_references_all[vtn].end(), s_atom[0] )!=d_type_references_all[vtn].end() ){
              d_tmodel[vv] = s_atom[0];
            }
          }
        }
      }else{
        if( d_neg_guard[s_lbl].find( s_atom )!=d_neg_guard[s_lbl].end() ){
          //check if the guard is asserted positively
          Node guard = d_neg_guard[s_lbl][s_atom];
          bool value;
          if( getValuation().hasSatValue( guard, value ) ) {
            assert_active[fact] = value;
          }
        }
      }
    }
    //(recursively) set inactive sub-assertions
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      if( !assert_active[fact] ){
        setInactiveAssertionRec( fact, lbl_to_assertions, assert_active );
      }
    }
    //set up model information based on active assertions
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      bool polarity = fact.getKind() != kind::NOT;
      TNode atom = polarity ? fact : fact[0];
      TNode s_atom = atom[0];
      TNode s_lbl = atom[1];
      if( assert_active[fact] ){
        computeLabelModel( s_lbl );
      }
    }
    //debug print
    if( Trace.isOn("sep-process") ){
      Trace("sep-process") << "--- Current spatial assertions : " << std::endl;
      for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
        Node fact = (*i);
        Trace("sep-process") << "  " << fact;
        if( !assert_active[fact] ){
          Trace("sep-process") << " [inactive]";
        }
        Trace("sep-process") << std::endl;
      }
      Trace("sep-process") << "---" << std::endl;
    }
    if(Trace.isOn("sep-eqc")) {
      eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator( &d_equalityEngine );
      Trace("sep-eqc") << "EQC:" << std::endl;
      while( !eqcs2_i.isFinished() ){
        Node eqc = (*eqcs2_i);
        eq::EqClassIterator eqc2_i = eq::EqClassIterator( eqc, &d_equalityEngine );
        Trace("sep-eqc") << "Eqc( " << eqc << " ) : { ";
        while( !eqc2_i.isFinished() ) {
          if( (*eqc2_i)!=eqc ){
            Trace("sep-eqc") << (*eqc2_i) << " ";
          }
          ++eqc2_i;
        }
        Trace("sep-eqc") << " } " << std::endl;
        ++eqcs2_i;
      }
      Trace("sep-eqc") << std::endl;
    }
    
    bool addedLemma = false;
    bool needAddLemma = false;
    //check negated star / positive wand
    if( options::sepCheckNeg() ){
      //get active labels
      std::map< Node, bool > active_lbl;
      if( options::sepMinimalRefine() ){
        for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
          Node fact = (*i);
          bool polarity = fact.getKind() != kind::NOT;
          TNode atom = polarity ? fact : fact[0];
          TNode s_atom = atom[0];
          bool use_polarity = s_atom.getKind()==kind::SEP_WAND ? !polarity : polarity;
          if( !use_polarity ){
            Assert( assert_active.find( fact )!=assert_active.end() );
            if( assert_active[fact] ){
              Assert( atom.getKind()==kind::SEP_LABEL );
              TNode s_lbl = atom[1];
              if( d_label_map[s_atom].find( s_lbl )!=d_label_map[s_atom].end() ){
                Trace("sep-process-debug") << "Active lbl : " << s_lbl << std::endl;
                active_lbl[s_lbl] = true;
              }
            }
          }
        }
      }

      //process spatial assertions
      for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
        Node fact = (*i);
        bool polarity = fact.getKind() != kind::NOT;
        TNode atom = polarity ? fact : fact[0];
        TNode s_atom = atom[0];

        bool use_polarity = s_atom.getKind()==kind::SEP_WAND ? !polarity : polarity;
        Trace("sep-process-debug") << "  check atom : " << s_atom << " use polarity " << use_polarity << std::endl;
        if( !use_polarity ){
          Assert( assert_active.find( fact )!=assert_active.end() );
          if( assert_active[fact] ){
            Assert( atom.getKind()==kind::SEP_LABEL );
            TNode s_lbl = atom[1];
            Trace("sep-process") << "--> Active negated atom : " << s_atom << ", lbl = " << s_lbl << std::endl;
            //add refinement lemma
            if( d_label_map[s_atom].find( s_lbl )!=d_label_map[s_atom].end() ){
              needAddLemma = true;
              TypeNode tn = getReferenceType( s_atom );
              tn = NodeManager::currentNM()->mkSetType(tn);
              //tn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(tn));
              Node o_b_lbl_mval = d_label_model[s_lbl].getValue( tn );
              Trace("sep-process") << "    Model for " << s_lbl << " : " << o_b_lbl_mval << std::endl;

              //get model values
              std::map< int, Node > mvals;
              for( std::map< int, Node >::iterator itl = d_label_map[s_atom][s_lbl].begin(); itl != d_label_map[s_atom][s_lbl].end(); ++itl ){
                Node sub_lbl = itl->second;
                int sub_index = itl->first;
                computeLabelModel( sub_lbl );
                Node lbl_mval = d_label_model[sub_lbl].getValue( tn );
                Trace("sep-process-debug") << "  child " << sub_index << " : " << sub_lbl << ", mval = " << lbl_mval << std::endl;
                mvals[sub_index] = lbl_mval;
              }
  
              // Now, assert model-instantiated implication based on the negation
              Assert( d_label_model.find( s_lbl )!=d_label_model.end() );
              std::vector< Node > conc;
              bool inst_success = true;
              //new refinement
              //instantiate the label
              std::map< Node, Node > visited;
              Node inst = instantiateLabel( s_atom, s_lbl, s_lbl, o_b_lbl_mval, visited, d_pto_model, tn, active_lbl );
              Trace("sep-inst-debug") << "    applied inst : " << inst << std::endl;
              if( inst.isNull() ){
                inst_success = false;
              }else{
                inst = Rewriter::rewrite( inst );
                if( inst==( polarity ? d_true : d_false ) ){
                  inst_success = false;
                }
                conc.push_back( polarity ? inst : inst.negate() );
              }
              if( inst_success ){
                std::vector< Node > lemc;
                Node pol_atom = atom;
                if( polarity ){
                  pol_atom = atom.negate();
                }
                lemc.push_back( pol_atom );

                //lemc.push_back( s_lbl.eqNode( o_b_lbl_mval ).negate() );
                //lemc.push_back( NodeManager::currentNM()->mkNode( kind::SUBSET, o_b_lbl_mval, s_lbl ).negate() );
                lemc.insert( lemc.end(), conc.begin(), conc.end() );
                Node lem = NodeManager::currentNM()->mkNode( kind::OR, lemc );
                if( std::find( d_refinement_lem[s_atom][s_lbl].begin(), d_refinement_lem[s_atom][s_lbl].end(), lem )==d_refinement_lem[s_atom][s_lbl].end() ){
                  d_refinement_lem[s_atom][s_lbl].push_back( lem );
                  Trace("sep-process") << "-----> refinement lemma (#" << d_refinement_lem[s_atom][s_lbl].size() << ") : " << lem << std::endl;
                  Trace("sep-lemma") << "Sep::Lemma : negated star/wand refinement : " << lem << std::endl;
                  d_out->lemma( lem );
                  addedLemma = true;
                }else{
                  //this typically should not happen, should never happen for complete base theories
                  Trace("sep-process") << "*** repeated refinement lemma : " << lem << std::endl;
                  Trace("sep-warn") << "TheorySep : WARNING : repeated refinement lemma : " << lem << "!!!" << std::endl;
                }
              }
            }else{
              Trace("sep-process-debug") << "  no children." << std::endl;
              Assert( s_atom.getKind()==kind::SEP_PTO || s_atom.getKind()==kind::SEP_EMP );
            }
          }else{
            Trace("sep-process-debug") << "--> inactive negated assertion " << s_atom << std::endl;
          }
        }
      }
      Trace("sep-process") << "...finished check of negated assertions, addedLemma=" << addedLemma << ", needAddLemma=" << needAddLemma << std::endl;
    }
    if( !addedLemma ){
      //must witness finite data points-to
      for( std::map< TypeNode, Node >::iterator it = d_base_label.begin(); it != d_base_label.end(); ++it ){
        TypeNode data_type = d_loc_to_data_type[it->first];
        //if the data type is finite
        if( data_type.isInterpretedFinite() ){
          computeLabelModel( it->second );
          Trace("sep-process-debug") << "Check heap data for " << it->first << " -> " << data_type << std::endl;
          for( unsigned j=0; j<d_label_model[it->second].d_heap_locs_model.size(); j++ ){
            Assert( d_label_model[it->second].d_heap_locs_model[j].getKind()==kind::SINGLETON );
            Node l = d_label_model[it->second].d_heap_locs_model[j][0];
            Trace("sep-process-debug") << "  location : " << l << std::endl;
            if( d_pto_model[l].isNull() ){
              needAddLemma = true;
              Node ll;
              std::map< Node, Node >::iterator itm = d_tmodel.find( l );
              if( itm!=d_tmodel.end() ) {
                ll = itm->second;
              }else{
                //try to assign arbitrary skolem?
              }
              if( !ll.isNull() ){
                Trace("sep-process") << "Must witness label : " << ll << ", data type is " << data_type << std::endl;
                Node dsk = NodeManager::currentNM()->mkSkolem( "dsk", data_type, "pto-data for implicit location" );
                // if location is in the heap, then something must point to it
                Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, NodeManager::currentNM()->mkNode( kind::MEMBER, ll, it->second ), 
                                                                            NodeManager::currentNM()->mkNode( kind::SEP_STAR,
                                                                              NodeManager::currentNM()->mkNode( kind::SEP_PTO, ll, dsk ),
                                                                              d_true ) );
                Trace("sep-lemma") << "Sep::Lemma : witness finite data-pto : " << lem << std::endl;
                d_out->lemma( lem );        
                addedLemma = true;     
              }else{
                //This should only happen if we are in an unbounded fragment
                Trace("sep-warn") << "TheorySep : WARNING : no term corresponding to location " << l << " in heap!!!" << std::endl;
              }
            }else{
              Trace("sep-process-debug") << "  points-to data witness : " << d_pto_model[l] << std::endl;
            }
          }
        }
      }
      if( !addedLemma ){
        //set up model
        Trace("sep-process-debug") << "...preparing sep model..." << std::endl;
        d_heap_locs_nptos.clear();
        //collect data points that are not pointed to
        for( context::CDList<Assertion>::const_iterator it = facts_begin(); it != facts_end(); ++ it) {
          Node lit = (*it).assertion;
          if( lit.getKind()==kind::NOT && lit[0].getKind()==kind::SEP_PTO ){
            Node s_atom = lit[0];
            Node v1 = d_valuation.getModel()->getRepresentative( s_atom[0] );
            Node v2 = d_valuation.getModel()->getRepresentative( s_atom[1] );
            Trace("sep-process-debug") << v1 << " does not point-to " << v2 << std::endl;
            d_heap_locs_nptos[v1].push_back( v2 );
          }
        }
        
        if( needAddLemma ){
          d_out->setIncomplete();
        }
      }
    }
  }
  Trace("sep-check") << "Sep::check(): " << e << " done, conflict=" << d_conflict.get() << endl;
}


bool TheorySep::needsCheckLastEffort() {
  return hasFacts();
}

Node TheorySep::getNextDecisionRequest( unsigned& priority ) {
  for( unsigned i=0; i<d_neg_guards.size(); i++ ){
    Node g = d_neg_guards[i];
    bool success = true;
    if( getLogicInfo().isQuantified() ){
      Assert( d_guard_to_assertion.find( g )!= d_guard_to_assertion.end() );
      Node a = d_guard_to_assertion[g];
      Node q = quantifiers::TermDb::getInstConstAttr( a );
      if( !q.isNull() ){
        //must wait to decide on counterexample literal from quantified formula
        Node cel = getQuantifiersEngine()->getTermDatabase()->getCounterexampleLiteral( q );
        bool value;
        if( d_valuation.hasSatValue( cel, value ) ){
          Trace("sep-dec-debug") << "TheorySep::getNextDecisionRequest : dependent guard " << g << " depends on value for guard for quantified formula : " << value << std::endl;
          success = value;
        }else{
          Trace("sep-dec-debug") << "TheorySep::getNextDecisionRequest : wait to decide on " << g << " until " << cel << " is set " << std::endl;
          success = false;
        }
      }
    }
    if( success ){
      bool value;
      if( !d_valuation.hasSatValue( g, value ) ) {
        Trace("sep-dec") << "TheorySep::getNextDecisionRequest : " << g << " (" << i << "/" << d_neg_guards.size() << ")" << std::endl;
        priority = 0;
        return g;
      }
    }
  }
  Trace("sep-dec-debug") << "TheorySep::getNextDecisionRequest : null" << std::endl;
  return Node::null();
}

void TheorySep::conflict(TNode a, TNode b) {
  Trace("sep-conflict") << "Sep::conflict : " << a << " " << b << std::endl;
  Node conflictNode = explain(a.eqNode(b));
  d_conflict = true;
  d_out->conflict( conflictNode );
}


TheorySep::HeapAssertInfo::HeapAssertInfo( context::Context* c ) : d_pto(c), d_has_neg_pto(c,false) {

}

TheorySep::HeapAssertInfo * TheorySep::getOrMakeEqcInfo( Node n, bool doMake ) {
  std::map< Node, HeapAssertInfo* >::iterator e_i = d_eqc_info.find( n );
  if( e_i==d_eqc_info.end() ){
    if( doMake ){
      HeapAssertInfo* ei = new HeapAssertInfo( getSatContext() );
      d_eqc_info[n] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*e_i).second;
  }
}

//for now, assume all constraints are for the same heap type (ensured by logic exceptions thrown in computeReferenceType2)
TypeNode TheorySep::getReferenceType( Node n ) {
  Assert( !d_type_ref.isNull() );
  return d_type_ref;
}

TypeNode TheorySep::getDataType( Node n ) {
  Assert( !d_type_data.isNull() );
  return d_type_data;
}

//must process assertions at preprocess so that quantified assertions are processed properly
void TheorySep::ppNotifyAssertions( std::vector< Node >& assertions ) {
  std::map< int, std::map< Node, int > > visited;
  std::map< int, std::map< Node, std::vector< Node > > > references;
  std::map< int, std::map< Node, bool > > references_strict;
  for( unsigned i=0; i<assertions.size(); i++ ){
    Trace("sep-pp") << "Process assertion : " << assertions[i] << std::endl;
    processAssertion( assertions[i], visited, references, references_strict, true, true, false );
  }
  //if data type is unconstrained, assume a fresh uninterpreted sort
  if( !d_type_ref.isNull() ){
    if( d_type_data.isNull() ){
      d_type_data = NodeManager::currentNM()->mkSort("_sep_U");
      Trace("sep-type") << "Sep: assume data type " << d_type_data << std::endl;
      d_loc_to_data_type[d_type_ref] = d_type_data;
    }
  }
}

//return cardinality
int TheorySep::processAssertion( Node n, std::map< int, std::map< Node, int > >& visited, 
                                 std::map< int, std::map< Node, std::vector< Node > > >& references, std::map< int, std::map< Node, bool > >& references_strict,
                                 bool pol, bool hasPol, bool underSpatial ) {
  int index = hasPol ? ( pol ? 1 : -1 ) : 0;
  int card = 0;
  std::map< Node, int >::iterator it = visited[index].find( n );
  if( it==visited[index].end() ){
    Trace("sep-pp-debug") << "process assertion : " << n << ", index = " << index << std::endl;
    if( n.getKind()==kind::SEP_EMP ){
      TypeNode tn = n[0].getType();
      TypeNode tnd = n[1].getType();
      registerRefDataTypes( tn, tnd, n );
      if( hasPol && pol ){
        references[index][n].clear();
        references_strict[index][n] = true; 
      }else{
        card = 1;
      }
    }else if( n.getKind()==kind::SEP_PTO ){
      TypeNode tn1 = n[0].getType();
      TypeNode tn2 = n[1].getType();
      registerRefDataTypes( tn1, tn2, n );
      if( quantifiers::TermDb::hasBoundVarAttr( n[0] ) ){
        if( d_bound_kind[tn1]!=bound_strict && d_bound_kind[tn1]!=bound_invalid ){
          if( options::quantEpr() && n[0].getKind()==kind::BOUND_VARIABLE ){
            // still valid : bound on heap models will include Herbrand universe of n[0].getType()
            d_bound_kind[tn1] = bound_herbrand;
          }else{
            d_bound_kind[tn1] = bound_invalid;
            Trace("sep-bound") << "reference cannot be bound (due to quantified pto)." << std::endl;
          }
        }
      }else{
        references[index][n].push_back( n[0] );
      }
      if( hasPol && pol ){
        references_strict[index][n] = true; 
      }else{
        card = 1;
      }
    }else{
      bool isSpatial = n.getKind()==kind::SEP_WAND || n.getKind()==kind::SEP_STAR;
      bool newUnderSpatial = underSpatial || isSpatial;
      bool refStrict = isSpatial;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bool newHasPol, newPol;
        QuantPhaseReq::getEntailPolarity( n, i, hasPol, pol, newHasPol, newPol );
        int newIndex = newHasPol ? ( newPol ? 1 : -1 ) : 0;
        int ccard = processAssertion( n[i], visited, references, references_strict, newPol, newHasPol, newUnderSpatial );
        //update cardinality
        if( n.getKind()==kind::SEP_STAR ){
          card += ccard;
        }else if( n.getKind()==kind::SEP_WAND ){
          if( i==1 ){
            card = ccard;
          }
        }else if( ccard>card ){
          card = ccard;
        }
        //track references if we are or below a spatial operator
        if( newUnderSpatial ){
          bool add = true;
          if( references_strict[newIndex].find( n[i] )!=references_strict[newIndex].end() ){
            if( !isSpatial ){
              if( references_strict[index].find( n )==references_strict[index].end() ){
                references_strict[index][n] = true;
              }else{
                add = false;
                //TODO: can derive static equality between sets
              }
            }
          }else{
            if( isSpatial ){
              refStrict = false;
            }
          }
          if( add ){
            for( unsigned j=0; j<references[newIndex][n[i]].size(); j++ ){
              if( std::find( references[index][n].begin(), references[index][n].end(), references[newIndex][n[i]][j] )==references[index][n].end() ){
                references[index][n].push_back( references[newIndex][n[i]][j] );
              }
            }
          }
        }
      }
      if( isSpatial && refStrict ){
        if( n.getKind()==kind::SEP_WAND ){
          //TODO
        }else{
          Assert( n.getKind()==kind::SEP_STAR && hasPol && pol );
          references_strict[index][n] = true;
        }
      }
    }
    visited[index][n] = card;
  }else{
    card = it->second;
  }
  
  if( !underSpatial && ( !references[index][n].empty() || card>0 ) ){
    TypeNode tn = getReferenceType( n );
    Assert( !tn.isNull() );
    // add references to overall type
    unsigned bt = d_bound_kind[tn];
    bool add = true;
    if( references_strict[index].find( n )!=references_strict[index].end() ){
      Trace("sep-bound") << "Strict bound found based on " << n << ", index = " << index << std::endl;
      if( bt!=bound_strict ){
        d_bound_kind[tn] = bound_strict;
        //d_type_references[tn].clear();
        d_card_max[tn] = card;
      }else{
        //TODO: derive static equality
        add = false;
      }
    }else{
      add = bt!=bound_strict;
    }
    for( unsigned i=0; i<references[index][n].size(); i++ ){
      if( std::find( d_type_references[tn].begin(), d_type_references[tn].end(), references[index][n][i] )==d_type_references[tn].end() ){
        d_type_references[tn].push_back( references[index][n][i] );
      }
    }
    if( add ){
      //add max cardinality
      if( card>(int)d_card_max[tn] ){
        d_card_max[tn] = card;
      }
    }
  }
  return card;
}

void TheorySep::registerRefDataTypes( TypeNode tn1, TypeNode tn2, Node atom ){
  //separation logic is effectively enabled when we find at least one spatial constraint occurs in the input
  if( options::incrementalSolving() ){
    std::stringstream ss;
    ss << "ERROR: cannot use separation logic in incremental mode." << std::endl;
    throw LogicException(ss.str());
  }
  std::map< TypeNode, TypeNode >::iterator itt = d_loc_to_data_type.find( tn1 );
  if( itt==d_loc_to_data_type.end() ){
    if( !d_loc_to_data_type.empty() ){
      TypeNode te1 = d_loc_to_data_type.begin()->first;
      std::stringstream ss;
      ss << "ERROR: specifying heap constraints for two different types : " << tn1 << " -> " << tn2 << " and " << te1 << " -> " << d_loc_to_data_type[te1] << std::endl;
      throw LogicException(ss.str());
      Assert( false );
    }
    if( tn2.isNull() ){
      Trace("sep-type") << "Sep: assume location type " << tn1 << " (from " << atom << ")" << std::endl;
    }else{
      Trace("sep-type") << "Sep: assume location type " << tn1 << " is associated with data type " << tn2 << " (from " << atom << ")" << std::endl;
    }
    d_loc_to_data_type[tn1] = tn2;
    //for now, we only allow heap constraints of one type
    d_type_ref = tn1;
    d_type_data = tn2;
    d_bound_kind[tn1] = bound_default;
  }else{
    if( !tn2.isNull() ){
      if( itt->second!=tn2 ){
        if( itt->second.isNull() ){
          Trace("sep-type") << "Sep: assume location type " << tn1 << " is associated with data type " << tn2 << " (from " << atom << ")" << std::endl;
          //now we know data type
          d_loc_to_data_type[tn1] = tn2;
          d_type_data = tn2;
        }else{
          std::stringstream ss;
          ss << "ERROR: location type " << tn1 << " is already associated with data type " << itt->second << ", offending atom is " << atom << " with data type " << tn2 << std::endl;
          throw LogicException(ss.str());
          Assert( false );
        }
      }
    }
  }
}

void TheorySep::initializeBounds() {
  if( !d_bounds_init ){
    Trace("sep-bound")  << "Initialize sep bounds..." << std::endl;
    d_bounds_init = true;
    for( std::map< TypeNode, TypeNode >::iterator it = d_loc_to_data_type.begin(); it != d_loc_to_data_type.end(); ++it ){
      TypeNode tn = it->first;
      Trace("sep-bound")  << "Initialize bounds for " << tn << "..." << std::endl;
      QuantEPR * qepr = getLogicInfo().isQuantified() ? getQuantifiersEngine()->getQuantEPR() : NULL;
      //if pto had free variable reference      
      if( d_bound_kind[tn]==bound_herbrand ){
        //include Herbrand universe of tn
        if( qepr && qepr->isEPR( tn ) ){
          for( unsigned j=0; j<qepr->d_consts[tn].size(); j++ ){
            Node k = qepr->d_consts[tn][j];
            if( std::find( d_type_references[tn].begin(), d_type_references[tn].end(), k )==d_type_references[tn].end() ){
              d_type_references[tn].push_back( k );
            }
          }
        }else{
          d_bound_kind[tn] = bound_invalid;
          Trace("sep-bound") << "reference cannot be bound (due to non-EPR variable)." << std::endl;
        }
      }
      unsigned n_emp = 0;
      if( d_bound_kind[tn] != bound_invalid ){
        n_emp = d_card_max[tn];  
      }else if( d_type_references[tn].empty() ){
        //must include at least one constant TODO: remove?
        n_emp = 1;
      }
      Trace("sep-bound") << "Cardinality element size : " << d_card_max[tn] << std::endl;
      Trace("sep-bound") << "Type reference size : " << d_type_references[tn].size() << std::endl;
      Trace("sep-bound") << "Constructing " << n_emp << " cardinality constants." << std::endl;
      for( unsigned r=0; r<n_emp; r++ ){
        Node e = NodeManager::currentNM()->mkSkolem( "e", tn, "cardinality bound element for seplog" );
        d_type_references_card[tn].push_back( e );
        d_type_ref_card_id[e] = r;
        //must include this constant back into EPR handling
        if( qepr && qepr->isEPR( tn ) ){
          qepr->addEPRConstant( tn, e );
        }
      }
      //EPR must include nil ref    
      if( qepr && qepr->isEPR( tn ) ){
        Node nr = getNilRef( tn );
        if( !qepr->isEPRConstant( tn, nr ) ){
          qepr->addEPRConstant( tn, nr );
        }
      }      
    }
  }
}

Node TheorySep::getBaseLabel( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_base_label.find( tn );
  if( it==d_base_label.end() ){
    initializeBounds();
    Trace("sep") << "Make base label for " << tn << std::endl;
    std::stringstream ss;
    ss << "__Lb";
    TypeNode ltn = NodeManager::currentNM()->mkSetType(tn);
    //TypeNode ltn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(tn));
    Node n_lbl = NodeManager::currentNM()->mkSkolem( ss.str(), ltn, "base label" );
    d_base_label[tn] = n_lbl;
    //make reference bound
    Trace("sep") << "Make reference bound label for " << tn << std::endl;
    std::stringstream ss2;
    ss2 << "__Lu";
    d_reference_bound[tn] = NodeManager::currentNM()->mkSkolem( ss2.str(), ltn, "" );
    d_type_references_all[tn].insert( d_type_references_all[tn].end(), d_type_references[tn].begin(), d_type_references[tn].end() );

    //check whether monotonic (elements can be added to tn without effecting satisfiability)
    bool tn_is_monotonic = true;
    if( tn.isSort() ){
      //TODO: use monotonicity inference
      tn_is_monotonic = !getLogicInfo().isQuantified();
    }else{
      tn_is_monotonic = tn.getCardinality().isInfinite();
    }
    //add a reference type for maximum occurrences of empty in a constraint
    if( options::sepDisequalC() && tn_is_monotonic ){
      for( unsigned r=0; r<d_type_references_card[tn].size(); r++ ){
        Node e = d_type_references_card[tn][r];
        //ensure that it is distinct from all other references so far
        for( unsigned j=0; j<d_type_references_all[tn].size(); j++ ){
          Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, e, d_type_references_all[tn][j] );
          d_out->lemma( eq.negate() );
        }
        d_type_references_all[tn].push_back( e );
      }
    }else{
      //break symmetries TODO
    
      d_type_references_all[tn].insert( d_type_references_all[tn].end(), d_type_references_card[tn].begin(), d_type_references_card[tn].end() );
    }
    //Assert( !d_type_references_all[tn].empty() );
    
    if( d_bound_kind[tn]!=bound_invalid ){      
      //construct bound
      d_reference_bound_max[tn] = mkUnion( tn, d_type_references_all[tn] );
      Trace("sep-bound") << "overall bound for " << d_base_label[tn] << " : " << d_reference_bound_max[tn] << std::endl;

      Node slem = NodeManager::currentNM()->mkNode( kind::SUBSET, d_base_label[tn], d_reference_bound_max[tn] );
      Trace("sep-lemma") << "Sep::Lemma: reference bound for " << tn << " : " << slem << std::endl;
      d_out->lemma( slem );
      //slem = NodeManager::currentNM()->mkNode( kind::SUBSET, d_base_label[tn], d_reference_bound_max[tn] );
      //Trace("sep-lemma") << "Sep::Lemma: base reference bound for " << tn << " : " << slem << std::endl;
      //d_out->lemma( slem );
      
      //symmetry breaking
      if( d_type_references_card[tn].size()>1 ){
        std::map< unsigned, Node > lit_mem_map;
        for( unsigned i=0; i<d_type_references_card[tn].size(); i++ ){
          lit_mem_map[i] = NodeManager::currentNM()->mkNode( kind::MEMBER, d_type_references_card[tn][i], d_reference_bound_max[tn]);
        }
        for( unsigned i=0; i<(d_type_references_card[tn].size()-1); i++ ){
          std::vector< Node > children;
          for( unsigned j=(i+1); j<d_type_references_card[tn].size(); j++ ){
            children.push_back( lit_mem_map[j].negate() );
          }
          if( !children.empty() ){
            Node sym_lem = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::AND, children );
            sym_lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, lit_mem_map[i].negate(), sym_lem );
            Trace("sep-lemma") << "Sep::Lemma: symmetry breaking lemma : " << sym_lem << std::endl;
            d_out->lemma( sym_lem );
          }
        }
      }
    }
    
    //assert that nil ref is not in base label
    Node nr = getNilRef( tn );
    Node nrlem = NodeManager::currentNM()->mkNode( kind::MEMBER, nr, n_lbl ).negate();
    Trace("sep-lemma") << "Sep::Lemma: sep.nil not in base label " << tn << " : " << nrlem << std::endl;
    d_out->lemma( nrlem );
    
    return n_lbl;
  }else{
    return it->second;
  }
}

Node TheorySep::getNilRef( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_nil_ref.find( tn );
  if( it==d_nil_ref.end() ){
    Node nil = NodeManager::currentNM()->mkUniqueVar( tn, kind::SEP_NIL );
    setNilRef( tn, nil );
    return nil;
  }else{
    return it->second;
  }
}

void TheorySep::setNilRef( TypeNode tn, Node n ) {
  Assert( n.getType()==tn );
  d_nil_ref[tn] = n;
}

Node TheorySep::mkUnion( TypeNode tn, std::vector< Node >& locs ) {
  Node u;
  if( locs.empty() ){
    TypeNode ltn = NodeManager::currentNM()->mkSetType(tn);
    return NodeManager::currentNM()->mkConst(EmptySet(ltn.toType()));
  }else{
    for( unsigned i=0; i<locs.size(); i++ ){
      Node s = locs[i];
      Assert( !s.isNull() );
      s = NodeManager::currentNM()->mkNode( kind::SINGLETON, s );
      if( u.isNull() ){
        u = s;
      }else{
        u = NodeManager::currentNM()->mkNode( kind::UNION, s, u );
      }
    }
    return u;
  }
}

Node TheorySep::getLabel( Node atom, int child, Node lbl ) {
  std::map< int, Node >::iterator it = d_label_map[atom][lbl].find( child );
  if( it==d_label_map[atom][lbl].end() ){
    TypeNode refType = getReferenceType( atom );
    std::stringstream ss;
    ss << "__Lc" << child;
    TypeNode ltn = NodeManager::currentNM()->mkSetType(refType);
    //TypeNode ltn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(refType));
    Node n_lbl = NodeManager::currentNM()->mkSkolem( ss.str(), ltn, "sep label" );
    d_label_map[atom][lbl][child] = n_lbl;
    d_label_map_parent[n_lbl] = lbl;
    return n_lbl;
  }else{
    return (*it).second;
  }
}

Node TheorySep::applyLabel( Node n, Node lbl, std::map< Node, Node >& visited ) {
  Assert( n.getKind()!=kind::SEP_LABEL );
  if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_WAND || n.getKind()==kind::SEP_PTO || n.getKind()==kind::SEP_EMP ){
    return NodeManager::currentNM()->mkNode( kind::SEP_LABEL, n, lbl );
  }else if( !n.getType().isBoolean() || n.getNumChildren()==0 ){
    return n;
  }else{
    std::map< Node, Node >::iterator it = visited.find( n );
    if( it==visited.end() ){
      std::vector< Node > children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node aln = applyLabel( n[i], lbl, visited );
        children.push_back( aln );
        childChanged = childChanged || aln!=n[i];
      }
      Node ret = n;
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
      visited[n] = ret;
      return ret;
    }else{
      return it->second;
    }
  }
}

Node TheorySep::instantiateLabel( Node n, Node o_lbl, Node lbl, Node lbl_v, std::map< Node, Node >& visited, std::map< Node, Node >& pto_model, 
                                  TypeNode rtn, std::map< Node, bool >& active_lbl, unsigned ind ) {
  Trace("sep-inst-debug") << "Instantiate label " << n << " " << lbl << " " << lbl_v << std::endl;
  if( options::sepMinimalRefine() && lbl!=o_lbl && active_lbl.find( lbl )!=active_lbl.end() ){
    Trace("sep-inst") << "...do not instantiate " << o_lbl << " since it has an active sublabel " << lbl << std::endl;
    return Node::null();
  }else{
    if( Trace.isOn("sep-inst") ){
      if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_WAND  || n.getKind()==kind::SEP_PTO || n.getKind()==kind::SEP_EMP ){
        for( unsigned j=0; j<ind; j++ ){ Trace("sep-inst") << "  "; }
        Trace("sep-inst") << n << "[" << lbl << "] :: " << lbl_v << std::endl;
      }
    }
    Assert( n.getKind()!=kind::SEP_LABEL );
    if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_WAND ){
      if( lbl==o_lbl ){
        std::vector< Node > children;
        children.resize( n.getNumChildren() );
        Assert( d_label_map[n].find( lbl )!=d_label_map[n].end() );
        std::map< int, Node > mvals;
        for( std::map< int, Node >::iterator itl = d_label_map[n][lbl].begin(); itl != d_label_map[n][lbl].end(); ++itl ){
          Node sub_lbl = itl->second;
          int sub_index = itl->first;
          Assert( sub_index>=0 && sub_index<(int)children.size() );
          Trace("sep-inst-debug") << "Sublabel " << sub_index << " is " << sub_lbl << std::endl;
          Node lbl_mval;
          if( n.getKind()==kind::SEP_WAND && sub_index==1 ){
            Assert( d_label_map[n][lbl].find( 0 )!=d_label_map[n][lbl].end() );
            Node sub_lbl_0 = d_label_map[n][lbl][0];
            computeLabelModel( sub_lbl_0 );
            Assert( d_label_model.find( sub_lbl_0 )!=d_label_model.end() );
            lbl_mval = NodeManager::currentNM()->mkNode( kind::UNION, lbl, d_label_model[sub_lbl_0].getValue( rtn ) );
          }else{
            computeLabelModel( sub_lbl );
            Assert( d_label_model.find( sub_lbl )!=d_label_model.end() );
            lbl_mval = d_label_model[sub_lbl].getValue( rtn );
          }
          Trace("sep-inst-debug") << "Sublabel value is " << lbl_mval  << std::endl;
          mvals[sub_index] = lbl_mval;
          children[sub_index] = instantiateLabel( n[sub_index], o_lbl, sub_lbl, lbl_mval, visited, pto_model, rtn, active_lbl, ind+1 );
          if( children[sub_index].isNull() ){
            return Node::null();
          }
        }
        Node empSet = NodeManager::currentNM()->mkConst(EmptySet(rtn.toType()));
        if( n.getKind()==kind::SEP_STAR ){

          //disjoint contraints
          std::vector< Node > conj;
          std::vector< Node > bchildren;
          bchildren.insert( bchildren.end(), children.begin(), children.end() );
          Node vsu;
          std::vector< Node > vs;
          for( std::map< int, Node >::iterator itl = d_label_map[n][lbl].begin(); itl != d_label_map[n][lbl].end(); ++itl ){
            Node sub_lbl = itl->second;
            Node lbl_mval = d_label_model[sub_lbl].getValue( rtn );
            for( unsigned j=0; j<vs.size(); j++ ){
              bchildren.push_back( NodeManager::currentNM()->mkNode( kind::INTERSECTION, lbl_mval, vs[j] ).eqNode( empSet ) );
            }
            vs.push_back( lbl_mval );
            if( vsu.isNull() ){
              vsu = lbl_mval;
            }else{
              vsu = NodeManager::currentNM()->mkNode( kind::UNION, vsu, lbl_mval );
            }
          }
          bchildren.push_back( vsu.eqNode( lbl ) );
          
          Assert( bchildren.size()>1 );
          conj.push_back( NodeManager::currentNM()->mkNode( kind::AND, bchildren ) );

          if( options::sepChildRefine() ){
            //child-specific refinements (TODO: use ?)
            for( unsigned i=0; i<children.size(); i++ ){
              std::vector< Node > tchildren;
              Node mval = mvals[i];
              tchildren.push_back( NodeManager::currentNM()->mkNode( kind::SUBSET, mval, lbl ) );            
              tchildren.push_back( children[i] );
              std::vector< Node > rem_children;
              for( unsigned j=0; j<children.size(); j++ ){
                if( j!=i ){
                  rem_children.push_back( n[j] );
                }
              }
              std::map< Node, Node > rvisited;
              Node rem = rem_children.size()==1 ? rem_children[0] : NodeManager::currentNM()->mkNode( kind::SEP_STAR, rem_children );
              rem = applyLabel( rem, NodeManager::currentNM()->mkNode( kind::SETMINUS, lbl, mval ), rvisited );
              tchildren.push_back( rem );
              conj.push_back( NodeManager::currentNM()->mkNode( kind::AND, tchildren ) );
            }
          }
          return conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( kind::OR, conj );
        }else{
          std::vector< Node > wchildren;
          //disjoint constraints
          Node sub_lbl_0 = d_label_map[n][lbl][0];
          Node lbl_mval_0 = d_label_model[sub_lbl_0].getValue( rtn );
          wchildren.push_back( NodeManager::currentNM()->mkNode( kind::INTERSECTION, lbl_mval_0, lbl ).eqNode( empSet ).negate() );
          
          //return the lemma
          wchildren.push_back( children[0].negate() );
          wchildren.push_back( children[1] );
          return NodeManager::currentNM()->mkNode( kind::OR, wchildren );
        }
      }else{
        //nested star/wand, label it and return
        return NodeManager::currentNM()->mkNode( kind::SEP_LABEL, n, lbl_v );
      }
    }else if( n.getKind()==kind::SEP_PTO ){
      //check if this pto reference is in the base label, if not, then it does not need to be added as an assumption
      Assert( d_label_model.find( o_lbl )!=d_label_model.end() );
      Node vr = d_valuation.getModel()->getRepresentative( n[0] );
      Node svr = NodeManager::currentNM()->mkNode( kind::SINGLETON, vr );
      bool inBaseHeap = std::find( d_label_model[o_lbl].d_heap_locs_model.begin(), d_label_model[o_lbl].d_heap_locs_model.end(), svr )!=d_label_model[o_lbl].d_heap_locs_model.end();
      Trace("sep-inst-debug") << "Is in base (non-instantiating) heap : " << inBaseHeap << " for value ref " << vr << " in " << o_lbl << std::endl;
      std::vector< Node > children;
      if( inBaseHeap ){
        Node s = NodeManager::currentNM()->mkNode( kind::SINGLETON, n[0] );
        children.push_back( NodeManager::currentNM()->mkNode( kind::SEP_LABEL, NodeManager::currentNM()->mkNode( kind::SEP_PTO, n[0], n[1] ), s ) );
      }else{
        //look up value of data
        std::map< Node, Node >::iterator it = pto_model.find( vr );
        if( it!=pto_model.end() ){
          if( n[1]!=it->second ){
            children.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n[1], it->second ) );
          }
        }else{
          Trace("sep-inst-debug") << "Data for " << vr << " was not specified, do not add condition." << std::endl;
        }
      } 
      children.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, NodeManager::currentNM()->mkNode( kind::SINGLETON, n[0] ), lbl_v ) );
      Node ret = children.empty() ? NodeManager::currentNM()->mkConst( true ) : ( children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::AND, children ) );
      Trace("sep-inst-debug") << "Return " << ret << std::endl;
      return ret;
    }else if( n.getKind()==kind::SEP_EMP ){
      //return NodeManager::currentNM()->mkConst( lbl_v.getKind()==kind::EMPTYSET );
      return lbl_v.eqNode( NodeManager::currentNM()->mkConst(EmptySet(lbl_v.getType().toType())) );
    }else{
      std::map< Node, Node >::iterator it = visited.find( n );
      if( it==visited.end() ){
        std::vector< Node > children;
        if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
          children.push_back( n.getOperator() );
        }
        bool childChanged = false;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node aln = instantiateLabel( n[i], o_lbl, lbl, lbl_v, visited, pto_model, rtn, active_lbl, ind );
          if( aln.isNull() ){
            return Node::null();
          }else{
            children.push_back( aln );
            childChanged = childChanged || aln!=n[i];
          }
        }
        Node ret = n;
        if( childChanged ){
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
        //careful about caching
        //visited[n] = ret;
        return ret;
      }else{
        return it->second;
      }
    }
  }
}

void TheorySep::setInactiveAssertionRec( Node fact, std::map< Node, std::vector< Node > >& lbl_to_assertions, std::map< Node, bool >& assert_active ) {
  Trace("sep-process-debug") << "setInactiveAssertionRec::inactive : " << fact << std::endl;
  assert_active[fact] = false;
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  TNode s_atom = atom[0];
  TNode s_lbl = atom[1];
  if( s_atom.getKind()==kind::SEP_WAND || s_atom.getKind()==kind::SEP_STAR ){
    for( unsigned j=0; j<s_atom.getNumChildren(); j++ ){
      Node lblc = getLabel( s_atom, j, s_lbl );
      for( unsigned k=0; k<lbl_to_assertions[lblc].size(); k++ ){
        setInactiveAssertionRec( lbl_to_assertions[lblc][k], lbl_to_assertions, assert_active );
      }
    }
  }
}

void TheorySep::getLabelChildren( Node s_atom, Node lbl, std::vector< Node >& children, std::vector< Node >& labels ) {
  for( unsigned i=0; i<s_atom.getNumChildren(); i++ ){
    Node lblc = getLabel( s_atom, i, lbl );
    Assert( !lblc.isNull() );
    std::map< Node, Node > visited;
    Node lc = applyLabel( s_atom[i], lblc, visited );
    Assert( !lc.isNull() );
    if( i==1 && s_atom.getKind()==kind::SEP_WAND ){
      lc = lc.negate();
    }
    children.push_back( lc );
    labels.push_back( lblc );
  }
  Assert( children.size()>1 );
}

void TheorySep::computeLabelModel( Node lbl ) {
  if( !d_label_model[lbl].d_computed ){
    d_label_model[lbl].d_computed = true;

    //we must get the value of lbl from the model: this is being run at last call, after the model is constructed
    //Assert(...); TODO
    Node v_val = d_valuation.getModel()->getRepresentative( lbl );
    Trace("sep-process") << "Model value (from valuation) for " << lbl << " : " << v_val << std::endl;
    if( v_val.getKind()!=kind::EMPTYSET ){
      while( v_val.getKind()==kind::UNION ){
        Assert( v_val[1].getKind()==kind::SINGLETON );
        d_label_model[lbl].d_heap_locs_model.push_back( v_val[1] );
        v_val = v_val[0];
      }
      if( v_val.getKind()==kind::SINGLETON ){
        d_label_model[lbl].d_heap_locs_model.push_back( v_val );
      }else{
        throw Exception("Could not establish value of heap in model.");
        Assert( false );
      }
    }
    for( unsigned j=0; j<d_label_model[lbl].d_heap_locs_model.size(); j++ ){
      Node u = d_label_model[lbl].d_heap_locs_model[j];
      Assert( u.getKind()==kind::SINGLETON );
      u = u[0];
      Node tt;
      std::map< Node, Node >::iterator itm = d_tmodel.find( u );
      if( itm==d_tmodel.end() ) {
        //Trace("sep-process") << "WARNING: could not find symbolic term in model for " << u << std::endl;
        //Assert( false );
        //tt = u;
        //TypeNode tn = u.getType().getRefConstituentType();
        TypeNode tn = u.getType();
        Trace("sep-process") << "WARNING: could not find symbolic term in model for " << u << ", cref type " << tn << std::endl;
        Assert( d_type_references_all.find( tn )!=d_type_references_all.end() );
        Assert( !d_type_references_all[tn].empty() );
        tt = d_type_references_all[tn][0];
      }else{
        tt = itm->second;
      }
      Node stt = NodeManager::currentNM()->mkNode( kind::SINGLETON, tt );
      Trace("sep-process-debug") << "...model : add " << tt << " for " << u << " in lbl " << lbl << std::endl;
      d_label_model[lbl].d_heap_locs.push_back( stt );
    }
  }
}

Node TheorySep::getRepresentative( Node t ) {
  if( d_equalityEngine.hasTerm( t ) ){
    return d_equalityEngine.getRepresentative( t );
  }else{
    return t;
  }
}

bool TheorySep::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheorySep::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheorySep::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    if( d_equalityEngine.areDisequal( a, b, false ) ){
      return true;
    }
  }
  return false;
}


void TheorySep::eqNotifyPreMerge(TNode t1, TNode t2) {

}

void TheorySep::eqNotifyPostMerge(TNode t1, TNode t2) {
  HeapAssertInfo * e2 = getOrMakeEqcInfo( t2, false );
  if( e2 && ( !e2->d_pto.get().isNull() || e2->d_has_neg_pto.get() ) ){
    HeapAssertInfo * e1 = getOrMakeEqcInfo( t1, true );
    if( !e2->d_pto.get().isNull() ){
      if( !e1->d_pto.get().isNull() ){
        Trace("sep-pto-debug") << "While merging " << t1 << " " << t2 << ", merge pto." << std::endl;
        mergePto( e1->d_pto.get(), e2->d_pto.get() );
      }else{
        e1->d_pto.set( e2->d_pto.get() );
      }
    }
    e1->d_has_neg_pto.set( e1->d_has_neg_pto.get() || e2->d_has_neg_pto.get() );
    //validate
    validatePto( e1, t1 );
  }
}

void TheorySep::validatePto( HeapAssertInfo * ei, Node ei_n ) {
  if( !ei->d_pto.get().isNull() && ei->d_has_neg_pto.get() ){
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      bool polarity = fact.getKind() != kind::NOT;
      if( !polarity ){
        TNode atom = polarity ? fact : fact[0];
        Assert( atom.getKind()==kind::SEP_LABEL );
        TNode s_atom = atom[0];
        if( s_atom.getKind()==kind::SEP_PTO ){
          if( areEqual( atom[1], ei_n ) ){
            addPto( ei, ei_n, atom, false );
          }
        }
      }
    }
    //we have now processed all pending negated pto
    ei->d_has_neg_pto.set( false );
  }
}

void TheorySep::addPto( HeapAssertInfo * ei, Node ei_n, Node p, bool polarity ) {
  Trace("sep-pto") << "Add pto " << p << ", pol = " << polarity << " to eqc " << ei_n << std::endl;
  if( !ei->d_pto.get().isNull() ){
    if( polarity ){
      Trace("sep-pto-debug") << "...eqc " << ei_n << " already has pto " << ei->d_pto.get() << ", merge." << std::endl;
      mergePto( ei->d_pto.get(), p );
    }else{
      Node pb = ei->d_pto.get();
      Trace("sep-pto") << "Process positive/negated pto " << " " << pb << " " << p << std::endl;
      Assert( pb.getKind()==kind::SEP_LABEL && pb[0].getKind()==kind::SEP_PTO );
      Assert( p.getKind()==kind::SEP_LABEL && p[0].getKind()==kind::SEP_PTO );
      Assert( areEqual( pb[1], p[1] ) );
      std::vector< Node > exp;
      if( pb[1]!=p[1] ){
        //if( pb[1].getKind()==kind::SINGLETON && p[1].getKind()==kind::SINGLETON ){
        //  exp.push_back( pb[1][0].eqNode( p[1][0] ) );
        //}else{
        exp.push_back( pb[1].eqNode( p[1] ) );
        //}
      }
      exp.push_back( pb );
      exp.push_back( p.negate() );
      std::vector< Node > conc;
      if( pb[0][1]!=p[0][1] ){
        conc.push_back( pb[0][1].eqNode( p[0][1] ).negate() );
      }
      //if( pb[1]!=p[1] ){
      //  conc.push_back( pb[1].eqNode( p[1] ).negate() );
      //}
      Node n_conc = conc.empty() ? d_false : ( conc.size()==1 ? conc[0] : NodeManager::currentNM()->mkNode( kind::OR, conc ) );
      Trace("sep-pto")  << "Conclusion is " << n_conc << std::endl;
      // propagation for (pto x y) ^ ~(pto z w) ^ x = z => y != w
      sendLemma( exp, n_conc, "PTO_NEG_PROP" );
    }
  }else{
    if( polarity ){
      ei->d_pto.set( p );
      validatePto( ei, ei_n );
    }else{
      ei->d_has_neg_pto.set( true );
    }
  }
}

void TheorySep::mergePto( Node p1, Node p2 ) {
  Trace("sep-lemma-debug") << "Merge pto " << p1 << " " << p2 << std::endl;
  Assert( p1.getKind()==kind::SEP_LABEL && p1[0].getKind()==kind::SEP_PTO );
  Assert( p2.getKind()==kind::SEP_LABEL && p2[0].getKind()==kind::SEP_PTO );
  if( !areEqual( p1[0][1], p2[0][1] ) ){
    std::vector< Node > exp;
    if( p1[1]!=p2[1] ){
      Assert( areEqual( p1[1], p2[1] ) );
      exp.push_back( p1[1].eqNode( p2[1] ) );
    }
    exp.push_back( p1 );
    exp.push_back( p2 );
    //enforces injectiveness of pto : (pto x y) ^ (pto y w) ^ x = y => y = w
    sendLemma( exp, p1[0][1].eqNode( p2[0][1] ), "PTO_PROP" );
  }
}

void TheorySep::sendLemma( std::vector< Node >& ant, Node conc, const char * c, bool infer ) {
  Trace("sep-lemma-debug") << "Do rewrite on inference : " << conc << std::endl;
  conc = Rewriter::rewrite( conc );
  Trace("sep-lemma-debug") << "Got : " << conc << std::endl;
  if( conc!=d_true ){
    if( infer && conc!=d_false ){
      Node ant_n;
      if( ant.empty() ){
        ant_n = d_true;
      }else if( ant.size()==1 ){
        ant_n = ant[0];
      }else{
        ant_n = NodeManager::currentNM()->mkNode( kind::AND, ant );
      }
      Trace("sep-lemma") << "Sep::Infer: " << conc << " from " << ant_n << " by " << c << std::endl;
      d_pending_exp.push_back( ant_n );
      d_pending.push_back( conc );
      d_infer.push_back( ant_n );
      d_infer_exp.push_back( conc );
    }else{
      std::vector< TNode > ant_e;
      for( unsigned i=0; i<ant.size(); i++ ){
        Trace("sep-lemma-debug") << "Explain : " << ant[i] << std::endl;
        explain( ant[i], ant_e );
      }
      Node ant_n;
      if( ant_e.empty() ){
        ant_n = d_true;
      }else if( ant_e.size()==1 ){
        ant_n = ant_e[0];
      }else{
        ant_n = NodeManager::currentNM()->mkNode( kind::AND, ant_e );
      }
      if( conc==d_false ){
        Trace("sep-lemma") << "Sep::Conflict: " << ant_n << " by " << c << std::endl;
        d_out->conflict( ant_n );
        d_conflict = true;
      }else{
        Trace("sep-lemma") << "Sep::Lemma: " << conc << " from " << ant_n << " by " << c << std::endl;
        d_pending_exp.push_back( ant_n );
        d_pending.push_back( conc );
        d_pending_lem.push_back( d_pending.size()-1 );
      }
    }
  }
}

void TheorySep::doPendingFacts() {
  if( d_pending_lem.empty() ){
    for( unsigned i=0; i<d_pending.size(); i++ ){
      if( d_conflict ){
        break;
      }
      Node atom = d_pending[i].getKind()==kind::NOT ? d_pending[i][0] : d_pending[i];
      bool pol = d_pending[i].getKind()!=kind::NOT;
      Trace("sep-pending") << "Sep : Assert to EE : " << atom << ", pol = " << pol << std::endl;
      if( atom.getKind()==kind::EQUAL ){
        d_equalityEngine.assertEquality(atom, pol, d_pending_exp[i]);
      }else{
        d_equalityEngine.assertPredicate(atom, pol, d_pending_exp[i]);
      }
    }
  }else{
    for( unsigned i=0; i<d_pending_lem.size(); i++ ){
      if( d_conflict ){
        break;
      }
      int index = d_pending_lem[i];
      Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, d_pending_exp[index], d_pending[index] );
      if( d_lemmas_produced_c.find( lem )==d_lemmas_produced_c.end() ){
        d_lemmas_produced_c.insert( lem );
        d_out->lemma( lem );
        Trace("sep-pending") << "Sep : Lemma : " << lem << std::endl;
      }
    }
  }
  d_pending_exp.clear();
  d_pending.clear();
  d_pending_lem.clear();
}

void TheorySep::debugPrintHeap( HeapInfo& heap, const char * c ) {
  Trace(c) << "[" << std::endl;
  Trace(c) << "  ";
  for( unsigned j=0; j<heap.d_heap_locs.size(); j++ ){
    Trace(c) << heap.d_heap_locs[j] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "]" << std::endl;
}

Node TheorySep::HeapInfo::getValue( TypeNode tn ) {
  Assert( d_heap_locs.size()==d_heap_locs_model.size() );
  if( d_heap_locs.empty() ){
    return NodeManager::currentNM()->mkConst(EmptySet(tn.toType()));
  }else if( d_heap_locs.size()==1 ){
    return d_heap_locs[0];
  }else{
    Node curr = NodeManager::currentNM()->mkNode( kind::UNION, d_heap_locs[0], d_heap_locs[1] );
    for( unsigned j=2; j<d_heap_locs.size(); j++ ){
      curr = NodeManager::currentNM()->mkNode( kind::UNION, curr, d_heap_locs[j] );
    }
    return curr;
  }
}

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
