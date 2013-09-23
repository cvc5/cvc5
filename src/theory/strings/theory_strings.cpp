/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: Tianyi Liang, Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/


#include "theory/strings/theory_strings.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/model.h"
#include "smt/logic_exception.h"
#include "theory/strings/options.h"
#include "theory/strings/type_enumerator.h"
#include <cmath>

using namespace std;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace strings {

TheoryStrings::TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe)
    : Theory(THEORY_STRINGS, c, u, out, valuation, logicInfo, qe),
    d_notify( *this ),
    d_equalityEngine(d_notify, c, "theory::strings::TheoryStrings"),
    d_conflict( c, false ),
    d_infer(c),
    d_infer_exp(c),
    d_nf_pairs(c),
    d_ind_map1(c),
    d_ind_map2(c),
    d_ind_map_exp(c),
    d_ind_map_lemma(c)
{
    // The kinds we are treating as function application in congruence
    d_equalityEngine.addFunctionKind(kind::STRING_IN_REGEXP);
    d_equalityEngine.addFunctionKind(kind::STRING_LENGTH);
    d_equalityEngine.addFunctionKind(kind::STRING_CONCAT);

    d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
    d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    d_true = NodeManager::currentNM()->mkConst( true );
    d_false = NodeManager::currentNM()->mkConst( false );
}

TheoryStrings::~TheoryStrings() {

}

void TheoryStrings::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryStrings::addSharedTerm(TNode t) {
  Debug("strings") << "TheoryStrings::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_STRINGS);
  Debug("strings") << "TheoryStrings::addSharedTerm() finished" << std::endl;
}

void TheoryStrings::propagate(Effort e)
{
  // direct propagation now
}

bool TheoryStrings::propagate(TNode literal) {
  Debug("strings-propagate") << "TheoryStrings::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("strings-propagate") << "TheoryStrings::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  Trace("strings-prop") << "strPropagate " << literal << std::endl;
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

/** explain */
void TheoryStrings::explain(TNode literal, std::vector<TNode>& assumptions){
  Debug("strings-explain") << "Explain " << literal << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

Node TheoryStrings::explain( TNode literal ){
  std::vector< TNode > assumptions;
  explain( literal, assumptions );
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::collectModelInfo( TheoryModel* m, bool fullModel ) {
	Trace("strings-model") << "TheoryStrings : Collect model info, fullModel = " << fullModel << std::endl;
	Trace("strings-model") << "TheoryStrings : assertEqualityEngine." << std::endl;
	m->assertEqualityEngine( &d_equalityEngine );
    // Generate model
	std::vector< Node > nodes;
	std::map< Node, Node > processed;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
    while( !eqcs_i.isFinished() ) {
        Node eqc = (*eqcs_i);
        //if eqc.getType is string
        if (eqc.getType().isString()) {
			/*
            EqcInfo* ei = getOrMakeEqcInfo( eqc );
            Node cst = ei ? ei->d_const_term : Node::null();
            if( !cst.isNull() ){
                //print out
                Trace("strings-model-debug") << cst << std::endl;
            }else{
                //is there a length term?
                //   is there a value for it?  if so, assign a constant via enumerator
                //   otherwise: error
                //otherwise: assign a new unique length, then assign a constant via enumerator
            }
			*/
			nodes.push_back( eqc );
        }else{
            //should be length eqc
            //if no constant, error
        }
        ++eqcs_i;
    }
	std::vector< std::vector< Node > > col;
	std::vector< Node > lts;
	seperateIntoCollections( nodes, col, lts );
	//step 1 : get all values for known lengths
	std::vector< Node > lts_values;
	//std::map< Node, bool > values_used;
	for( unsigned i=0; i<col.size(); i++ ){
		Trace("strings-model") << "Checking length for " << col[i][0] << " (length is " << lts[i] << ")" << std::endl;
		if( lts[i].isConst() ){
			lts_values.push_back( lts[i] );
			//values_used[ lts[i] ] = true;
		}else{
			//get value for lts[i];
			if( !lts[i].isNull() ){
				Node v = d_valuation.getModelValue(lts[i]);
				//Node v = m->getValue(lts[i]);
				Trace("strings-model") << "Model value for " << lts[i] << " is " << v << std::endl;
				lts_values.push_back( v );
				//values_used[ v ] = true;
			}else{
				Trace("strings-model-warn") << "No length for eqc " << col[i][0] << std::endl;
				Assert( false );
				lts_values.push_back( Node::null() );
			}
		}
	}
	////step 2 : assign arbitrary values for unknown lengths?
	//for( unsigned i=0; i<col.size(); i++ ){
	//	if( 
	//}
	Trace("strings-model") << "Assign to equivalence classes..." << std::endl;
	//step 3 : assign values to equivalence classes that are pure variables
	for( unsigned i=0; i<col.size(); i++ ){
		std::vector< Node > pure_eq;
		Trace("strings-model") << "The equivalence classes ";
		for( unsigned j=0; j<col[i].size(); j++ ) {
			Trace("strings-model") << col[i][j] << " ";
			//check if col[i][j] has only variables
			EqcInfo* ei = getOrMakeEqcInfo( col[i][j], false );
            Node cst = ei ? ei->d_const_term : Node::null();
			if( cst.isNull() ){
				Assert( d_normal_forms.find( col[i][j] )!=d_normal_forms.end() );
				if( d_normal_forms[col[i][j]].size()==1 && d_normal_forms[col[i][j]][0]==col[i][j] ){
					pure_eq.push_back( col[i][j] );
				}
			}else{
				processed[col[i][j]] = cst;
			}
		}
		Trace("strings-model") << "have length " << lts_values[i] << std::endl;
		
		Trace("strings-model") << "*** Need to assign values of length " << lts_values[i] << " to equivalence classes ";
		for( unsigned j=0; j<pure_eq.size(); j++ ){
			Trace("strings-model") << pure_eq[j] << " ";
		}
		Trace("strings-model") << std::endl;

		//use type enumerator
		StringEnumeratorLength sel(lts_values[i].getConst<Rational>().getNumerator().toUnsignedInt());
		for( unsigned j=0; j<pure_eq.size(); j++ ){
			Assert( !sel.isFinished() );
			Node c = *sel;
			while( d_equalityEngine.hasTerm( c ) ){
				++sel;
				Assert( !sel.isFinished() );
				c = *sel;
			}
			++sel;
			Trace("strings-model") << "Assigned constant " << c << " for " << pure_eq[j] << std::endl;
			processed[pure_eq[j]] = c;
			m->assertEquality( pure_eq[j], c, true );
		}
	}
	Trace("strings-model") << "String Model : Finished." << std::endl;
	//step 4 : assign constants to all other equivalence classes
	for( unsigned i=0; i<nodes.size(); i++ ){
		if( processed.find( nodes[i] )==processed.end() ){
			Assert( d_normal_forms.find( nodes[i] )!=d_normal_forms.end() );
			std::vector< Node > nc;
			for( unsigned j=0; j<d_normal_forms[nodes[i]].size(); j++ ) {
				Assert( processed.find( d_normal_forms[nodes[i]][j] )!=processed.end() );
				nc.push_back(processed[d_normal_forms[nodes[i]][j]]);
			}
			Node cc = mkConcat( nc );
			Assert( cc.getKind()==kind::CONST_STRING );
			Trace("strings-model") << "Determined constant " << cc << " for " << nodes[i] << std::endl;
			processed[nodes[i]] = cc;
			m->assertEquality( nodes[i], cc, true );
		}
	}
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void TheoryStrings::preRegisterTerm(TNode n) {
  Debug("strings-prereg") << "TheoryStrings::preRegisterTerm() " << n << endl;
  //collectTerms( n );
  switch (n.getKind()) {
  case kind::EQUAL:
    d_equalityEngine.addTriggerEquality(n);
    break;
  case kind::STRING_IN_REGEXP:
    d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
    if(n.getKind() == kind::VARIABLE || n.getKind()==kind::SKOLEM) {
	  if( std::find( d_length_intro_vars.begin(), d_length_intro_vars.end(), n )==d_length_intro_vars.end() ){
		  Node n_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n);
		  Node n_len_geq_zero = NodeManager::currentNM()->mkNode( kind::GEQ, n_len, d_zero);
		  Trace("strings-lemma") << "Strings: Add lemma " << n_len_geq_zero << std::endl;
		  d_out->lemma(n_len_geq_zero);
	  }
    }
    if (n.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(n);
    } else {
      // Function applications/predicates
      d_equalityEngine.addTerm(n);
    }
    break;
  }
}

void TheoryStrings::dealPositiveWordEquation(TNode n) {
  Trace("strings-pwe") << "Deal Positive Word Equation: " << n << endl;
  Node node = n;

  // length left = length right
  //Node n_left = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[0]);
  //Node n_right = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[1]);
  if(node[0].getKind() == kind::CONST_STRING) {
  } else if(node[0].getKind() == kind::STRING_CONCAT) {
  }
}

void TheoryStrings::check(Effort e) {
  bool polarity;
  TNode atom;

 // Trace("strings-process") << "Theory of strings, check : " << e << std::endl;
  Trace("strings-check") << "Theory of strings, check : " << e << std::endl;
  while ( !done() && !d_conflict)
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("strings-assertion") << "get assertion: " << fact << endl;

    polarity = fact.getKind() != kind::NOT;
    atom = polarity ? fact : fact[0];
    if (atom.getKind() == kind::EQUAL) {
      //head
      //if(atom[0].getKind() == kind::CONST_STRING) {
          //if(atom[1].getKind() == kind::STRING_CONCAT) {
          //}
      //}
      //tail
      d_equalityEngine.assertEquality(atom, polarity, fact);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
    switch(atom.getKind()) {
        case kind::EQUAL:
            if(polarity) {
                //if(atom[0].isString() && atom[1].isString()) {
                    //dealPositiveWordEquation(atom);
                //}
            } else {
                // TODO: Word Equation negaitive
            }
            break;
        case kind::STRING_IN_REGEXP:
            // TODO: membership
            break;
        default:
            //possibly error
            break;
    }
  }
  doPendingFacts();


  bool addedLemma = false;
  if( e == EFFORT_FULL && !d_conflict ) {
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
      while( !eqcs_i.isFinished() ){
        Node eqc = (*eqcs_i);
        //if eqc.getType is string
        if (eqc.getType().isString()) {
            //EqcInfo* ei = getOrMakeEqcInfo( eqc, true );
            //get the constant for the equivalence class
            //int c_len = ...;
            eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
            while( !eqc_i.isFinished() ){
              Node n = (*eqc_i);

              //if n is concat, and
              //if n has not instantiatied the concat..length axiom
              //then, add lemma
              if( n.getKind() == kind::STRING_CONCAT || n.getKind() == kind::CONST_STRING ){
                if( d_length_inst.find(n)==d_length_inst.end() ){
                    d_length_inst[n] = true;
                    Trace("strings-debug") << "get n: " << n << endl;
                    Node sk = NodeManager::currentNM()->mkSkolem( "lsym_$$", n.getType(), "created for concat lemma" );
					d_length_intro_vars.push_back( sk );
                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, sk, n );
                    eq = Rewriter::rewrite(eq);
                    Trace("strings-lemma") << "Strings: Add lemma " << eq << std::endl;
                    d_out->lemma(eq);
                    Node skl = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
                    Node lsum;
                    if( n.getKind() == kind::STRING_CONCAT ){
                        //add lemma
                        std::vector<Node> node_vec;
                        for( unsigned i=0; i<n.getNumChildren(); i++ ) {
                            Node lni = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n[i] );
                            node_vec.push_back(lni);
                        }
                        lsum = NodeManager::currentNM()->mkNode( kind::PLUS, node_vec );
                    }else{
                        //add lemma
                        lsum = NodeManager::currentNM()->mkConst( ::CVC4::Rational( n.getConst<String>().size() ) );
                    }
                    Node ceq = NodeManager::currentNM()->mkNode( kind::EQUAL, skl, lsum );
                    ceq = Rewriter::rewrite(ceq);
                    Trace("strings-lemma") << "Strings: Add lemma " << ceq << std::endl;
                    d_out->lemma(ceq);
                    addedLemma = true;
                }
              }
              ++eqc_i;
            }
        }
        ++eqcs_i;
  }
  if( !addedLemma ){
      addedLemma = checkNormalForms();
      if(!d_conflict && !addedLemma) {
          addedLemma = checkCardinality();
          if( !d_conflict && !addedLemma ){
            addedLemma = checkInductiveEquations();
          }
      }
  }
  }
  Trace("strings-process") << "Theory of strings, done check : " << e << std::endl;
}

TheoryStrings::EqcInfo::EqcInfo(  context::Context* c ) : d_const_term(c), d_length_term(c), d_cardinality_lem_k(c) {

}

TheoryStrings::EqcInfo * TheoryStrings::getOrMakeEqcInfo( Node eqc, bool doMake ) {
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( eqc );
  if( eqc_i==d_eqc_info.end() ){
    if( doMake ){
      EqcInfo* ei = new EqcInfo( getSatContext() );
      d_eqc_info[eqc] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*eqc_i).second;
  }
}


/** Conflict when merging two constants */
void TheoryStrings::conflict(TNode a, TNode b){
  Node conflictNode;
  if (a.getKind() == kind::CONST_BOOLEAN) {
    conflictNode = explain( a.iffNode(b) );
  } else {
    conflictNode = explain( a.eqNode(b) );
  }
  Debug("strings-conflict") << "CONFLICT: Eq engine conflict : " << conflictNode << std::endl;
  d_out->conflict( conflictNode );
  d_conflict = true;
}

/** called when a new equivalance class is created */
void TheoryStrings::eqNotifyNewClass(TNode t){
  if( t.getKind() == kind::CONST_STRING ){
    EqcInfo * ei =getOrMakeEqcInfo( t, true );
    ei->d_const_term = t;
  }
  if( t.getKind() == kind::STRING_LENGTH ){
    Trace("strings-debug") << "New length eqc : " << t << std::endl;
    Node r = d_equalityEngine.getRepresentative(t[0]);
    EqcInfo * ei = getOrMakeEqcInfo( r, true );
    ei->d_length_term = t[0];
  }
}

/** called when two equivalance classes will merge */
void TheoryStrings::eqNotifyPreMerge(TNode t1, TNode t2){
    EqcInfo * e2 = getOrMakeEqcInfo(t2, false);
    if( e2 ){
        EqcInfo * e1 = getOrMakeEqcInfo( t1 );
        //add information from e2 to e1
        if( !e2->d_const_term.get().isNull() ){
            e1->d_const_term.set( e2->d_const_term );
        }
        if( !e2->d_length_term.get().isNull() ){
            e1->d_length_term.set( e2->d_length_term );
        }
        if( e2->d_cardinality_lem_k.get()>e1->d_cardinality_lem_k.get() ) {
            e1->d_cardinality_lem_k.set( e2->d_cardinality_lem_k );
        }
    }
    if( hasTerm( d_zero ) ){
        Node leqc;
        if( areEqual(d_zero, t1) ){
            leqc = t2;
        }else if( areEqual(d_zero, t2) ){
            leqc = t1;
        }
        if( !leqc.isNull() ){
            //scan equivalence class to see if we apply
            eq::EqClassIterator eqc_i = eq::EqClassIterator( leqc, &d_equalityEngine );
            while( !eqc_i.isFinished() ){
              Node n = (*eqc_i);
              if( n.getKind()==kind::STRING_LENGTH ){
                if( !hasTerm( d_emptyString ) || !areEqual(n[0], d_emptyString ) ){
                    Trace("strings-debug") << "Processing possible inference." << n << std::endl;
                    //apply the rule length(n[0])==0 => n[0] == ""
                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, n[0], d_emptyString );
                    d_pending.push_back( eq );
                    Node eq_exp = NodeManager::currentNM()->mkNode( kind::EQUAL, n, d_zero );
                    d_pending_exp[eq] = eq_exp;
                    Trace("strings-infer") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
                    d_infer.push_back(eq);
                    d_infer_exp.push_back(eq_exp);
                }
              }
              ++eqc_i;
            }
        }
    }
}

/** called when two equivalance classes have merged */
void TheoryStrings::eqNotifyPostMerge(TNode t1, TNode t2) {

}

/** called when two equivalance classes are disequal */
void TheoryStrings::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {

}

void TheoryStrings::computeCareGraph(){
  Theory::computeCareGraph();
}

void TheoryStrings::doPendingFacts() {
  int i=0;
  while( !d_conflict && i<(int)d_pending.size() ){
    Node fact = d_pending[i];
    Node exp = d_pending_exp[ fact ];
      Trace("strings-pending") << "Process pending fact : " << fact << " from " << exp << std::endl;
      bool polarity = fact.getKind() != kind::NOT;
      TNode atom = polarity ? fact : fact[0];
      if (atom.getKind() == kind::EQUAL) {
        d_equalityEngine.assertEquality( atom, polarity, exp );
      }else{
        d_equalityEngine.assertPredicate( atom, polarity, exp );
      }
    i++;
  }
  d_pending.clear();
  d_pending_exp.clear();
}

void TheoryStrings::getNormalForms(Node &eqc, std::vector< Node > & visited, std::vector< Node > & nf,
    std::vector< std::vector< Node > > &normal_forms,  std::vector< std::vector< Node > > &normal_forms_exp, std::vector< Node > &normal_form_src) {
    // EqcItr
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ) {
        Node n = (*eqc_i);
        Trace("strings-process") << "Process term " << n << std::endl;
        if( n.getKind() == kind::CONST_STRING || n.getKind() == kind::STRING_CONCAT ) {
            std::vector<Node> nf_n;
            std::vector<Node> nf_exp_n;
            if( n.getKind() == kind::CONST_STRING  ){
                if( n!=d_emptyString ) {
                    nf_n.push_back( n );
                }
            } else if( n.getKind() == kind::STRING_CONCAT ) {
                for( unsigned i=0; i<n.getNumChildren(); i++ ) {
                    Node nr = d_equalityEngine.getRepresentative( n[i] );
                    std::vector< Node > nf_temp;
                    std::vector< Node > nf_exp_temp;
                    Trace("strings-process") << "Normalizing subterm " << n[i] << " = "  << nr << std::endl;
                    normalizeEquivalenceClass( nr, visited, nf_temp, nf_exp_temp );
                    if( d_conflict || !d_pending.empty() || !d_lemma_cache.empty() ) {
                        return;
                    }
                    if( nf.size()!=1 || nf[0]!=d_emptyString ) {
                        for( unsigned r=0; r<nf_temp.size(); r++ ) {
                            Assert( nf_temp[r].getKind()!=kind::STRING_CONCAT );
                        }
                        nf_n.insert( nf_n.end(), nf_temp.begin(), nf_temp.end() );
                    }
                    nf_exp_n.insert( nf_exp_n.end(), nf_exp_temp.begin(), nf_exp_temp.end() );
                    if( nr!=n[i] ) {
                        nf_exp_n.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n[i], nr ) );
                    }
                }
            }
            normal_forms.push_back(nf_n);
            normal_forms_exp.push_back(nf_exp_n);
            normal_form_src.push_back(n);
        }
        /* should we add these?
        else {
            //var/sk?
            std::vector<Node> nf_n;
            std::vector<Node> nf_exp_n;
            nf_n.push_back(n);
            normal_forms.push_back(nf_n);
            normal_forms_exp.push_back(nf_exp_n);
            normal_form_src.push_back(n);
        }*/
        ++eqc_i;
    }

    // Test the result
    if( !normal_forms.empty() ) {
        Trace("strings-solve") << "--- Normal forms for equivlance class " << eqc << " : " << std::endl;
        for( unsigned i=0; i<normal_forms.size(); i++ ) {
            Trace("strings-solve") << "#" << i << " (from " << normal_form_src[i] << ") : ";
            for( unsigned j=0; j<normal_forms[i].size(); j++ ) {
                if(j>0) Trace("strings-solve") << ", ";
                Trace("strings-solve") << normal_forms[i][j];
            }
            Trace("strings-solve") << std::endl;
            Trace("strings-solve") << "   Explanation is : ";
            if(normal_forms_exp[i].size() == 0) {
                Trace("strings-solve") << "NONE";
            } else {
                for( unsigned j=0; j<normal_forms_exp[i].size(); j++ ) {
                    if(j>0) Trace("strings-solve") << " AND ";
                    Trace("strings-solve") << normal_forms_exp[i][j];
                }
            }
            Trace("strings-solve") << std::endl;
        }
    }
}
//nf_exp is conjunction
void TheoryStrings::normalizeEquivalenceClass( Node eqc, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp ) {
    Trace("strings-process") << "Process equivalence class " << eqc << std::endl;
    if( std::find( visited.begin(), visited.end(), eqc )!=visited.end() ){
        //nf.push_back( eqc );
        if( eqc.getKind()==kind::STRING_CONCAT ){
            for( unsigned i=0; i<eqc.getNumChildren(); i++ ){
                nf.push_back( eqc[i] );
            }
        }else{
            nf.push_back( eqc );
        }
        Trace("strings-process") << "Return process equivalence class " << eqc << " : already visited." << std::endl;
    } else if (d_equalityEngine.hasTerm(d_emptyString) && d_equalityEngine.areEqual( eqc, d_emptyString )){
        //do nothing
        Trace("strings-process") << "Return process equivalence class " << eqc << " : empty." << std::endl;
		d_normal_forms[eqc].clear();
		d_normal_forms_exp[eqc].clear();
    } else {
        visited.push_back( eqc );
        if(d_normal_forms.find(eqc)==d_normal_forms.end() ){
            //phi => t = s1 * ... * sn
            // normal form for each non-variable term in this eqc (s1...sn)
            std::vector< std::vector< Node > > normal_forms;
            // explanation for each normal form (phi)
            std::vector< std::vector< Node > > normal_forms_exp;
            // record terms for each normal form (t)
            std::vector< Node > normal_form_src;
            //Get Normal Forms
            getNormalForms(eqc, visited, nf, normal_forms, normal_forms_exp, normal_form_src);
            if( d_conflict || !d_pending.empty() || !d_lemma_cache.empty() ) {
                return;
            }

            unsigned i = 0;
            //unify each normal form > 0 with normal_forms[0]
            for( unsigned j=1; j<normal_forms.size(); j++ ) {
                std::vector< Node > loop_eqs_x;
                std::vector< Node > loop_eqs_y;
                std::vector< Node > loop_eqs_z;
                std::vector< Node > loop_exps;
                Trace("strings-solve") << "Process normal form #0 against #" << j << "..." << std::endl;
                if( isNormalFormPair( normal_form_src[i], normal_form_src[j] ) ){
                    Trace("strings-solve") << "Already normalized (in cache)." << std::endl;
                }else{
                    Trace("strings-solve") << "Not in cache." << std::endl;
                    //the current explanation for why the prefix is equal
                    std::vector< Node > curr_exp;
                    curr_exp.insert(curr_exp.end(), normal_forms_exp[i].begin(), normal_forms_exp[i].end() );
                    curr_exp.insert(curr_exp.end(), normal_forms_exp[j].begin(), normal_forms_exp[j].end() );
                    curr_exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, normal_form_src[i], normal_form_src[j] ) );
                    //ensure that normal_forms[i] and normal_forms[j] are the same modulo equality
                    unsigned index_i = 0;
                    unsigned index_j = 0;
                    bool success;
                    do
                    {
                        success = false;
                        //if we are at the end
                        if(index_i==normal_forms[i].size() || index_j==normal_forms[j].size() ) {
                            if( index_i==normal_forms[i].size() && index_j==normal_forms[j].size() ){
                                //we're done
                                addNormalFormPair( normal_form_src[i], normal_form_src[j] );
                                //add loop equations that we've accumulated
                                for( unsigned r=0; r<loop_eqs_x.size(); r++ ){
                                    addInductiveEquation( loop_eqs_x[r], loop_eqs_y[r], loop_eqs_z[r], loop_exps[r] );
                                }
                            }else{
                                //the remainder must be empty
                                unsigned k = index_i==normal_forms[i].size() ? j : i;
                                unsigned index_k = index_i==normal_forms[i].size() ? index_j : index_i;
                                while(!d_conflict && index_k<normal_forms[k].size()) {
                                    //can infer that this string must be empty
                                    Node eq_exp;
                                    if( curr_exp.empty() ) {
                                        eq_exp = d_true;
                                    } else if( curr_exp.size() == 1 ) {
                                        eq_exp = curr_exp[0];
                                    } else {
                                        eq_exp = NodeManager::currentNM()->mkNode( kind::AND, curr_exp );
                                    }
                                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, d_emptyString, normal_forms[k][index_k] );
                                    Trace("strings-lemma") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
                                    //d_equalityEngine.assertEquality( eq, true, eq_exp );
                                    d_pending.push_back( eq );
                                    d_pending_exp[eq] = eq_exp;
                                    d_infer.push_back(eq);
                                    d_infer_exp.push_back(eq_exp);
                                    index_k++;
                                }
                            }
                        }else {
                            Trace("strings-solve-debug") << "Process " << normal_forms[i][index_i] << " ... " << normal_forms[j][index_j] << std::endl;
                            if(areEqual(normal_forms[i][index_i],normal_forms[j][index_j])){
                                Trace("strings-solve-debug") << "Case 1 : strings are equal" << std::endl;
                                //terms are equal, continue
                                if( normal_forms[i][index_i]!=normal_forms[j][index_j] ){
                                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL,normal_forms[i][index_i],
                                                                                                     normal_forms[j][index_j]);
                                    Trace("strings-solve-debug") << "Add to explanation : " << eq << std::endl;
                                    curr_exp.push_back(eq);
                                }
                                index_j++;
                                index_i++;
                                success = true;
                            }else{
                                EqcInfo * ei = getOrMakeEqcInfo( normal_forms[i][index_i] );
                                Node length_term_i = ei->d_length_term;
                                if( length_term_i.isNull()) {
                                    //typically shouldnt be necessary
                                    length_term_i = normal_forms[i][index_i];
                                }
                                length_term_i = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, length_term_i );
                                EqcInfo * ej = getOrMakeEqcInfo( normal_forms[j][index_j] );
                                Node length_term_j = ej->d_length_term;
                                if( length_term_j.isNull()) {
                                    length_term_j = normal_forms[j][index_j];
                                }
                                length_term_j = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, length_term_j );
                                //check if length(normal_forms[i][index]) == length(normal_forms[j][index])
                                if( areEqual(length_term_i, length_term_j)  ){
                                    Trace("strings-solve-debug") << "Case 2 : string lengths are equal" << std::endl;
                                    //length terms are equal, merge equivalence classes if not already done so
                                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[i][index_i], normal_forms[j][index_j] );
                                    std::vector< Node > temp_exp;
                                    temp_exp.insert(temp_exp.end(), curr_exp.begin(), curr_exp.end() );
                                    temp_exp.push_back(NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ));
                                    Node eq_exp = temp_exp.empty() ? d_true :
                                                    temp_exp.size() == 1 ? temp_exp[0] : NodeManager::currentNM()->mkNode( kind::AND, temp_exp );
                                    Trace("strings-lemma") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
                                    //d_equalityEngine.assertEquality( eq, true, eq_exp );
                                    d_pending.push_back( eq );
                                    d_pending_exp[eq] = eq_exp;
                                    d_infer.push_back(eq);
                                    d_infer_exp.push_back(eq_exp);
                                    return;
                                }else{
                                    Trace("strings-solve-debug") << "Case 3 : must compare strings" << std::endl;
                                    Node conc;
                                    std::vector< Node > antec;
                                    std::vector< Node > antec_new_lits;
                                    //check for loops
                                    //Trace("strings-loop") << "Check for loops i,j = " << (index_i+1) << "/" << normal_forms[i].size() << " " << (index_j+1) << "/" << normal_forms[j].size() << std::endl;
                                    int has_loop[2] = { -1, -1 };
                                    for( unsigned r=0; r<2; r++ ){
                                        int index = (r==0 ? index_i : index_j);
                                        int other_index = (r==0 ? index_j : index_i );
                                        int n_index = (r==0 ? i : j);
                                        int other_n_index = (r==0 ? j : i);
                                        if( normal_forms[other_n_index][other_index].getKind() != kind::CONST_STRING ) {
                                            for( unsigned lp = index+1; lp<normal_forms[n_index].size(); lp++ ){
                                                if( normal_forms[n_index][lp]==normal_forms[other_n_index][other_index] ){
                                                    has_loop[r] = lp;
                                                    break;
                                                }
                                            }
                                        }
                                    }
									Node term_t;
									Node term_s;
                                    if( has_loop[0]!=-1 || has_loop[1]!=-1 ){
                                        int loop_n_index = has_loop[0]!=-1 ? i : j;
                                        int other_n_index = has_loop[0]!=-1 ? j : i;
                                        int loop_index = has_loop[0]!=-1 ? has_loop[0] : has_loop[1];
                                        int index = has_loop[0]!=-1 ? index_i : index_j;
                                        int other_index = has_loop[0]!=-1 ? index_j : index_i;
                                        Trace("strings-loop") << "Detected possible loop for " << normal_forms[loop_n_index][loop_index];
                                        Trace("strings-loop") << " ... " << normal_forms[other_n_index][other_index] << std::endl;
										int found_size_y = -1;
                                        //we have x * s1 * .... * sm = t1 * ... * tn * x * r1 * ... * rp
                                        //check if
                                        //t1 * ... * tn = n[loop_n_index][index]....n[loop_n_index][loop_index-1] = y * z
                                        // and
                                        //s1 * ... * sk = n[other_n_index][other_index+1].....n[other_n_index][k+1] = z * y
                                        // for some y,z,k
										std::vector< Node > tc;
										for( int r=index; r<loop_index; r++ ){
											tc.push_back( normal_forms[loop_n_index][r] );
										}
										term_t = mkConcat( tc );
										std::vector< Node > sc;
										for( int r=other_index+1; r<(int)normal_forms[other_n_index].size(); r++ ){
											sc.push_back( normal_forms[other_n_index][r] );
										}
										term_s = mkConcat( sc );
										Trace("strings-loop") << "Find y,z from t,s = " << term_t << ", " << term_s << std::endl;
										/*TODO:incomplete*/
										if( term_t==term_s ){
											found_size_y = -2;
										}else if( term_t.getKind()==kind::STRING_CONCAT && term_s.getKind()==kind::STRING_CONCAT ){
											for( int size_y = 0; size_y<(int)term_t.getNumChildren(); size_y++ ){
												int size_z = term_t.getNumChildren()-size_y;
												bool success = true;
												//check for z
												for( int r = 0; r<size_z; r++ ){
													if( r >= (int)term_s.getNumChildren() ||
														term_s[r]!=term_t[size_y+r] ) {
														Trace("strings-loop") << "Failed z for size_y = " << size_y << " at index " << r << std::endl;
														success = false;
														break;
													}
												}
												//check for y
												if( success ){
													for( int r=0; r<size_y; r++ ){
														if( (size_y+r) >= (int)term_s.getNumChildren() ||
															term_s[size_y+r]!=term_t[r] ) {
															success = false;
															Trace("strings-loop") << "Failed y for size_y = " << size_y << " at index " << r << std::endl;
															break;
														}
													}
													if( success ){
														found_size_y = size_y;
														break;
													}
												}
											}
										}
										/*TODO: incomplete*/
                                        if( found_size_y==-1 ){
											Trace("strings-loop") << "Must add lemma." << std::endl;
                                            //need to break
                                            Node sk_y= NodeManager::currentNM()->mkSkolem( "ldssym_$$", normal_forms[i][index_i].getType(), "created for loop detection split" );
                                            Node sk_z= NodeManager::currentNM()->mkSkolem( "ldssym_$$", normal_forms[i][index_i].getType(), "created for loop detection split" );

                                            antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
                                            //t1 * ... * tn = y * z
                                            std::vector< Node > c1c;
                                            //n[loop_n_index][index]....n[loop_n_index][loop_lindex-1]
                                            for( int r=index; r<=loop_index-1; r++ ) {
                                                c1c.push_back( normal_forms[loop_n_index][r] );
                                            }
                                            Node conc1 = mkConcat( c1c );
                                            conc1 = NodeManager::currentNM()->mkNode( kind::EQUAL, conc1,
                                                            NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk_y, sk_z ) );
                                            std::vector< Node > c2c;
                                            //s1 * ... * sk = n[other_n_index][other_index+1].....n[other_n_index][k+1]
                                            for( int r=other_index+1; r < (int)normal_forms[other_n_index].size(); r++ ) {
                                                c2c.push_back( normal_forms[other_n_index][r] );
                                            }
                                            Node left2 = mkConcat( c2c );
                                            std::vector< Node > c3c;
                                            c3c.push_back( sk_z );
                                            c3c.push_back( sk_y );
                                            //r1 * ... * rk = n[loop_n_index][loop_index+1]....n[loop_n_index][loop_index-1]
                                            for( int r=loop_index+1; r < (int)normal_forms[loop_n_index].size(); r++ ) {
                                                c3c.push_back( normal_forms[loop_n_index][r] );
                                            }
                                            Node conc2 = NodeManager::currentNM()->mkNode( kind::EQUAL, left2,
                                                            mkConcat( c3c ) );
                                            Node sk_y_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk_y );
                                            Node sk_z_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk_z );
                                            //Node sk_z_len_gt_zero = NodeManager::currentNM()->mkNode( kind::GT, sk_z_len, d_zero);
											Node len_y_eq_zero = NodeManager::currentNM()->mkNode( kind::EQUAL, sk_y_len, d_zero);
											Node len_z_eq_zero = NodeManager::currentNM()->mkNode( kind::EQUAL, sk_z_len, d_zero);
											Node yz_imp_zz = NodeManager::currentNM()->mkNode( kind::IMPLIES, len_z_eq_zero, len_y_eq_zero);

                                            conc = NodeManager::currentNM()->mkNode( kind::AND, conc1, conc2, yz_imp_zz );//sk_z_len_gt_zero, yz_imp_zz
                                            Node loop_x = normal_forms[other_n_index][other_index];
                                            Node loop_y = sk_y;
                                            Node loop_z = sk_z;
                                            //we will be done
                                            addNormalFormPair( normal_form_src[i], normal_form_src[j] );
											Node ant = mkExplain( antec, antec_new_lits );
											sendLemma( ant, conc, "Loop" );
											addInductiveEquation( loop_x, loop_y, loop_z, ant );
											return;
                                        } else {
											// x = (yz)*y
											Trace("strings-loop") << "We have that " << normal_forms[loop_n_index][loop_index] << " = (";
											loop_eqs_x.push_back( normal_forms[loop_n_index][loop_index] );
											if( found_size_y==-2 ){
												//TODO: incomplete for cases like aa.x=x.aa => x=(aa)* | (aa)*a
												Trace("strings-loop") << " " << term_t << " ) * " << std::endl;
												loop_eqs_y.push_back( d_emptyString );
												loop_eqs_z.push_back( term_t );
											}else{
												for( unsigned r=0; r<2; r++ ){
													//print y
													std::vector< Node > yc;
													for( int rr = 0; rr<found_size_y; rr++ ){
														if( rr>0 ) Trace("strings-loop") << ".";
														Trace("strings-loop") << term_t[rr];
														yc.push_back( term_t[rr] );
													}
													if( r==0 ){
														loop_eqs_y.push_back( mkConcat( yc ) );
														Trace("strings-loop") <<"..";
														//print z
														int found_size_z = term_t.getNumChildren()-found_size_y;
														std::vector< Node > zc;
														for( int rr = 0; rr<found_size_z; rr++ ){
															if( rr>0 ) Trace("strings-loop") << ".";
															Trace("strings-loop") << term_t[found_size_y+rr];
															zc.push_back( term_t[found_size_y+rr] );
														}
														Trace("strings-loop") << ")*";
														loop_eqs_z.push_back( mkConcat( zc ) );
													}
												}
											}
                                            Trace("strings-loop") << std::endl;
                                            if( loop_n_index==(int)i ){
                                                index_j += (loop_index+1)-index_i;
                                                index_i = loop_index+1;
                                            }else{
                                                index_i += (loop_index+1)-index_j;
                                                index_j = loop_index+1;
                                            }
                                            success = true;
                                            std::vector< Node > empty_vec;
                                            loop_exps.push_back( mkExplain( curr_exp, empty_vec ) );
                                        }
                                    }else{
                                        Trace("strings-solve-debug") << "No loops detected." << std::endl;
                                        if( normal_forms[i][index_i].getKind() == kind::CONST_STRING ||
                                            normal_forms[j][index_j].getKind() == kind::CONST_STRING) {
											unsigned const_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? i : j;
											unsigned const_index_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? index_i : index_j;
											unsigned nconst_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? j : i;
											unsigned nconst_index_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? index_j : index_i;
                                            Node const_str = normal_forms[const_k][const_index_k];
                                            Node other_str = normal_forms[nconst_k][nconst_index_k];
                                            if( other_str.getKind() == kind::CONST_STRING ) {
                                                unsigned len_short = const_str.getConst<String>().size() <= other_str.getConst<String>().size() ? const_str.getConst<String>().size() : other_str.getConst<String>().size();
                                                if( const_str.getConst<String>().strncmp(other_str.getConst<String>(), len_short) ) {
                                                    //same prefix
                                                    //k is the index of the string that is shorter
                                                    int k = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? i : j;
                                                    int index_k = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? index_i : index_j;
                                                    int l = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? j : i;
                                                    int index_l = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? index_j : index_i;
                                                    Node remainderStr = NodeManager::currentNM()->mkConst( normal_forms[l][index_l].getConst<String>().substr(len_short) );
                                                    Trace("strings-solve-debug-test") << "Break normal form of " << normal_forms[l][index_l] << " into " << normal_forms[k][index_k] << ", " << remainderStr << std::endl;
                                                    normal_forms[l].insert( normal_forms[l].begin()+index_l + 1, remainderStr );
                                                    normal_forms[l][index_l] = normal_forms[k][index_k];
                                                    success = true;
                                                } else {
                                                    //curr_exp is conflict
                                                    antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
													Node ant = mkExplain( antec, antec_new_lits );
													sendLemma( ant, conc, "Conflict" );
													return;
                                                }
                                            } else {
                                                Assert( other_str.getKind()!=kind::STRING_CONCAT );
                                                antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
												if( nconst_index_k==normal_forms[nconst_k].size()-1 ){
													std::vector< Node > eqn;
													for( unsigned r=0; r<2; r++ ){
														int index_k = r==0 ? index_i : index_j;
														int k = r==0 ? i : j;
														std::vector< Node > eqnc;
														for( unsigned index_l=index_k; index_l<normal_forms[k].size(); index_l++ ){
															eqnc.push_back( normal_forms[k][index_l] );
														}
														eqn.push_back( mkConcat( eqnc ) );
													}
													conc = eqn[0].eqNode( eqn[1] );
												}else{
													Node firstChar = const_str.getConst<String>().size() == 1 ? const_str :
														NodeManager::currentNM()->mkConst( const_str.getConst<String>().substr(0, 1) );
													//split the string
													Node sk = NodeManager::currentNM()->mkSkolem( "ssym_$$", normal_forms[i][index_i].getType(), "created for split" );

													Node eq1 = NodeManager::currentNM()->mkNode( kind::EQUAL, other_str, d_emptyString );
													Node eq2_m = NodeManager::currentNM()->mkNode( kind::EQUAL, other_str,
																NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, firstChar, sk ) );
													Node eq2 = eq2_m;//NodeManager::currentNM()->mkNode( kind::AND, eq2_m, sk_len_geq_zero );
													conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );
												}
                                                Trace("strings-solve-debug") << "Break normal form constant/variable " << std::endl;

												Node ant = mkExplain( antec, antec_new_lits );
												sendLemma( ant, conc, "Constant Split" );
												return;
                                            }
                                        }else{
                                            antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
                                            Node ldeq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ).negate();
                                            if( d_equalityEngine.areDisequal( length_term_i, length_term_j, true ) ){
                                                antec.push_back( ldeq );
                                            }else{
                                                antec_new_lits.push_back(ldeq);
                                            }
                                            Node sk = NodeManager::currentNM()->mkSkolem( "ssym_$$", normal_forms[i][index_i].getType(), "created for split" );
                                            Node eq1 = NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[i][index_i],
                                                        NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, normal_forms[j][index_j], sk ) );
                                            Node eq2 = NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[j][index_j],
                                                        NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, normal_forms[i][index_i], sk ) );
                                            conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );
                                            // |sk| > 0
                                            Node sk_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
                                            Node sk_gt_zero = NodeManager::currentNM()->mkNode( kind::GT, sk_len, d_zero);
                                            Trace("strings-lemma") << "Strings lemma : " << sk_gt_zero << std::endl;
                                            //d_out->lemma(sk_gt_zero);
                                            d_lemma_cache.push_back( sk_gt_zero );

											Node ant = mkExplain( antec, antec_new_lits );
											sendLemma( ant, conc, "Split" );
											return;
                                        }
                                    }
                                }
                            }
                        }
                    }while(success);
                }
            }

            //construct the normal form
            if( normal_forms.empty() ){
                Trace("strings-solve-debug2") << "construct the normal form" << std::endl;
                nf.push_back( eqc );
            } else {
                Trace("strings-solve-debug2") << "just take the first normal form" << std::endl;
                //just take the first normal form
                nf.insert( nf.end(), normal_forms[0].begin(), normal_forms[0].end() );
                nf_exp.insert( nf_exp.end(), normal_forms_exp[0].begin(), normal_forms_exp[0].end() );
                if( eqc!=normal_form_src[0] ){
                    nf_exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, eqc, normal_form_src[0] ) );
                }
                Trace("strings-solve-debug2") << "just take the first normal form ... done" << std::endl;
            }
            //if( visited.empty() ){
                //TODO : cache?
            //}
            d_normal_forms[eqc].insert( d_normal_forms[eqc].end(), nf.begin(), nf.end() );
            d_normal_forms_exp[eqc].insert( d_normal_forms_exp[eqc].end(), nf_exp.begin(), nf_exp.end() );
            Trace("strings-process") << "Return process equivalence class " << eqc << " : returned." << std::endl;
        }else{
            Trace("strings-process") << "Return process equivalence class " << eqc << " : already computed." << std::endl;
            nf.insert( nf.end(), d_normal_forms[eqc].begin(), d_normal_forms[eqc].end() );
            nf_exp.insert( nf_exp.end(), d_normal_forms_exp[eqc].begin(), d_normal_forms_exp[eqc].end() );
        }
        visited.pop_back();
    }
}
bool TheoryStrings::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryStrings::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

void TheoryStrings::addNormalFormPair( Node n1, Node n2 ) {
  if( !isNormalFormPair( n1, n2 ) ){
        NodeList* lst;
        NodeListMap::iterator nf_i = d_nf_pairs.find( n1 );
        if( nf_i == d_nf_pairs.end() ){
          if( d_nf_pairs.find( n2 )!=d_nf_pairs.end() ){
            addNormalFormPair( n2, n1 );
            return;
          }
          lst = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
          d_nf_pairs.insertDataFromContextMemory( n1, lst );
		  Trace("strings-nf") << "Create cache for " << n1 << std::endl;
        }else{
          lst = (*nf_i).second;
        }
		Trace("strings-nf") << "Add normal form pair : " << n1 << " " << n2 << std::endl;
        lst->push_back( n2 );
		Assert( isNormalFormPair( n1, n2 ) );
    }else{
		Trace("strings-nf-debug") << "Already a normal form pair " << n1 << " " << n2 << std::endl;
	}

}
bool TheoryStrings::isNormalFormPair( Node n1, Node n2 ) {
    //TODO: modulo equality?
    return isNormalFormPair2( n1, n2 ) || isNormalFormPair2( n2, n1 );
}
bool TheoryStrings::isNormalFormPair2( Node n1, Node n2 ) {
    //Trace("strings-debug") << "is normal form pair. " << n1 << " " << n2 << std::endl;
  NodeList* lst;
  NodeListMap::iterator nf_i = d_nf_pairs.find( n1 );
  if( nf_i != d_nf_pairs.end() ){
    lst = (*nf_i).second;
    for( NodeList::const_iterator i = lst->begin(); i != lst->end(); ++i ) {
        Node n = *i;
        if( n==n2 ){
            return true;
        }
    }
  }
  return false;
}

void TheoryStrings::addInductiveEquation( Node x, Node y, Node z, Node exp ) {
    Trace("strings-solve-debug") << "add inductive equation for " << x << " = (" << y << " " << z << ")* " << y << std::endl;

    NodeListMap::iterator itr_x_y = d_ind_map1.find(x);
    NodeList* lst1;
    NodeList* lst2;
    NodeList* lste;
    NodeList* lstl;
    if( itr_x_y == d_ind_map1.end() ) {
        // add x->y
        lst1 = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
        d_ind_map1.insertDataFromContextMemory( x, lst1 );
        // add x->z
        lst2 = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
        d_ind_map2.insertDataFromContextMemory( x, lst2 );
        // add x->exp
        lste = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
        d_ind_map_exp.insertDataFromContextMemory( x, lste );
        // add x->hasLemma false
        lstl = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
        d_ind_map_lemma.insertDataFromContextMemory( x, lstl );
    } else {
        //TODO: x in (yz)*y (exp) vs  x in (y1 z1)*y1 (exp1)
        lst1 = (*itr_x_y).second;
        lst2 = (*d_ind_map2.find(x)).second;
        lste = (*d_ind_map_exp.find(x)).second;
        lstl = (*d_ind_map_lemma.find(x)).second;
        Trace("strings-solve-debug") << "Already in maps " << x << " = (" << lst1 << " " << lst2 << ")* " << lst1 << std::endl;
        Trace("strings-solve-debug") << "... with exp = " << lste << std::endl;
    }
    lst1->push_back( y );
    lst2->push_back( z );
    lste->push_back( exp );
}

void TheoryStrings::sendLemma( Node ant, Node conc, const char * c ) {
	if( conc.isNull() ){
		d_out->conflict(ant);
		Trace("strings-conflict") << "CONFLICT : Strings conflict : " << ant << std::endl;
		d_conflict = true;
	}else{
		Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, ant, conc );
		Trace("strings-lemma") << "Strings " << c << " lemma : " << lem << std::endl;
		//d_out->lemma(lem);
		d_lemma_cache.push_back( lem );
	}
}

Node TheoryStrings::mkConcat( std::vector< Node >& c ) {
    Node cc = c.size()>1 ? NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, c ) : ( c.size()==1 ? c[0] : d_emptyString );
	return Rewriter::rewrite( cc );
}

Node TheoryStrings::mkExplain( std::vector< Node >& a, std::vector< Node >& an ) {
    std::vector< TNode > antec_exp;
    for( unsigned i=0; i<a.size(); i++ ){
        Trace("strings-solve-debug") << "Ask for explanation of " << a[i] << std::endl;
        //assert
        if(a[i].getKind() == kind::EQUAL) {
            //assert( hasTerm(a[i][0]) );
            //assert( hasTerm(a[i][1]) );
            Assert( areEqual(a[i][0], a[i][1]) );
        } else if( a[i].getKind()==kind::NOT && a[i][0].getKind()==kind::EQUAL ){
            Assert( hasTerm(a[i][0][0]) );
            Assert( hasTerm(a[i][0][1]) );
            Assert( d_equalityEngine.areDisequal(a[i][0][0], a[i][0][1], true) );
        }
		unsigned ps = antec_exp.size();
        explain(a[i], antec_exp);
        Trace("strings-solve-debug") << "Done, explanation was : " << std::endl;
		for( unsigned j=ps; j<antec_exp.size(); j++ ){
			Trace("strings-solve-debug") << "  " << antec_exp[j] << std::endl;
		}
		Trace("strings-solve-debug") << std::endl;
    }
    for( unsigned i=0; i<an.size(); i++ ){
		Trace("strings-solve-debug") << "Add to explanation (new literal) " << an[i] << std::endl;
        antec_exp.push_back(an[i]);
    }
    Node ant;
    if( antec_exp.empty() ) {
        ant = d_true;
    } else if( antec_exp.size()==1 ) {
        ant = antec_exp[0];
    } else {
        ant = NodeManager::currentNM()->mkNode( kind::AND, antec_exp );
    }
	ant = Rewriter::rewrite( ant );
    return ant;
}

bool TheoryStrings::checkNormalForms() {
    Trace("strings-process") << "Normalize equivalence classes...." << std::endl;
	eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator( &d_equalityEngine );
	for( unsigned t=0; t<2; t++ ){
		Trace("strings-eqc") << (t==0 ? "STRINGS:" : "OTHER:") << std::endl;
		while( !eqcs2_i.isFinished() ){
		Node eqc = (*eqcs2_i);
		bool print = (t==0 && eqc.getType().isString() ) || (t==1 && !eqc.getType().isString() );
		if (print) {
			eq::EqClassIterator eqc2_i = eq::EqClassIterator( eqc, &d_equalityEngine );
			Trace("strings-eqc") << "Eqc( " << eqc << " ) : ";
			while( !eqc2_i.isFinished() ) {
				if( (*eqc2_i)!=eqc ){
					Trace("strings-eqc") << (*eqc2_i) << " ";
				}
				++eqc2_i;
			}
			Trace("strings-eqc") << std::endl;
		}
		++eqcs2_i;
		}
		Trace("strings-eqc") << std::endl;
	}
	Trace("strings-eqc") << std::endl;
	for( NodeListMap::const_iterator it = d_nf_pairs.begin(); it != d_nf_pairs.end(); ++it ){
		NodeList* lst = (*it).second;
		NodeList::const_iterator it2 = lst->begin();
		Trace("strings-nf") << (*it).first << " has been unified with ";
		while( it2!=lst->end() ){
			Trace("strings-nf") << (*it2);
			++it2;
		}
		Trace("strings-nf") << std::endl;
	}
	Trace("strings-nf") << std::endl;

  bool addedFact = false;
  do {
    //calculate normal forms for each equivalence class, possibly adding splitting lemmas
    d_normal_forms.clear();
    d_normal_forms_exp.clear();
    std::map< Node, Node > nf_to_eqc;
    std::map< Node, Node > eqc_to_exp;
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
      d_lemma_cache.clear();
      while( !eqcs_i.isFinished() ){
        Node eqc = (*eqcs_i);
        //if eqc.getType is string
        if (eqc.getType().isString()) {
            Trace("strings-process") << "Verify normal forms are the same for " << eqc << std::endl;
            std::vector< Node > visited;
            std::vector< Node > nf;
            std::vector< Node > nf_exp;
            normalizeEquivalenceClass(eqc, visited, nf, nf_exp);
            if( d_conflict ){
                return true;
            }else if ( d_pending.empty() && d_lemma_cache.empty() ){
                Node nf_term;
                if( nf.size()==0 ){
                    nf_term = d_emptyString;
                }else if( nf.size()==1 ) {
                    nf_term = nf[0];
                } else {
                    nf_term = NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, nf );
                }
                nf_term = Rewriter::rewrite( nf_term );
                Trace("strings-debug") << "Make nf_term_exp..." << std::endl;
                Node nf_term_exp = nf_exp.empty() ? d_true :
                                    nf_exp.size()==1 ? nf_exp[0] : NodeManager::currentNM()->mkNode( kind::AND, nf_exp );
                if( nf_to_eqc.find(nf_term)!=nf_to_eqc.end() ){
                    //Trace("strings-debug") << "Merge because of normal form : " << eqc << " and " << nf_to_eqc[nf_term] << " both have normal form " << nf_term << std::endl;
                    //two equivalence classes have same normal form, merge
                    Node eq_exp = NodeManager::currentNM()->mkNode( kind::AND, nf_term_exp, eqc_to_exp[nf_to_eqc[nf_term]] );
                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, eqc, nf_to_eqc[nf_term] );
                    Trace("strings-lemma") << "Strings (by normal forms) : Infer " << eq << " from " << eq_exp << std::endl;
                    //d_equalityEngine.assertEquality( eq, true, eq_exp );
                    d_pending.push_back( eq );
                    d_pending_exp[eq] = eq_exp;
                    d_infer.push_back(eq);
                    d_infer_exp.push_back(eq_exp);
                }else{
                    nf_to_eqc[nf_term] = eqc;
                    eqc_to_exp[eqc] = nf_term_exp;
                }
            }
            Trace("strings-process") << "Done verifying normal forms are the same for " << eqc << std::endl;
        }
        ++eqcs_i;
      }
      addedFact = !d_pending.empty();
      doPendingFacts();
      if( !d_conflict ){
          for( unsigned i=0; i<d_lemma_cache.size(); i++ ){
              Trace("strings-pending") << "Process pending lemma : " << d_lemma_cache[i] << std::endl;
              d_out->lemma( d_lemma_cache[i] );
          }
          if( !d_lemma_cache.empty() ){
            d_lemma_cache.clear();
            return true;
          }
      }
  } while (!d_conflict && addedFact);
  return false;
}

bool TheoryStrings::checkCardinality() {
  int cardinality = options::stringCharCardinality();
  Trace("strings-solve-debug2") << "get cardinality: " << cardinality << endl;

  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  std::vector< Node > eqcs;
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    //if eqc.getType is string
    if (eqc.getType().isString()) {
		eqcs.push_back( eqc );
	}
	++eqcs_i;
  }
  std::vector< std::vector< Node > > cols;
  std::vector< Node > lts;
  seperateIntoCollections( eqcs, cols, lts );

  for( unsigned i = 0; i<cols.size(); ++i ){
    Node lr = lts[i];
    Trace("string-cardinality") << "Number of strings with length equal to " << lr << " is " << cols[i].size() << std::endl;
    // size > c^k
    double k = std::log( cols[i].size() ) / log((double) cardinality);
    unsigned int int_k = (unsigned int)k;
    Node k_node = NodeManager::currentNM()->mkConst( ::CVC4::Rational( int_k ) );
    //double c_k = pow ( (double)cardinality, (double)lr );
    if( cols[i].size() > 1 ) {
        bool allDisequal = true;
        for( std::vector< Node >::iterator itr1 = cols[i].begin();
              itr1 != cols[i].end(); ++itr1) {
            for( std::vector< Node >::iterator itr2 = itr1 + 1;
                  itr2 != cols[i].end(); ++itr2) {
                if(!d_equalityEngine.areDisequal( *itr1, *itr2, false )) {
                    allDisequal = false;
                    // add split lemma
                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, *itr1, *itr2 );
                    Node neq = NodeManager::currentNM()->mkNode( kind::NOT, eq );
                    Node lemma_or = NodeManager::currentNM()->mkNode( kind::OR, eq, neq );
                    Trace("strings-lemma") << "Strings split lemma : " << lemma_or << std::endl;
                    d_out->lemma(lemma_or);
                    return true;
                }
            }
        }
        if(allDisequal) {
            EqcInfo* ei = getOrMakeEqcInfo( lr, true );
            Trace("string-cardinality") << "Previous cardinality used for " << lr << " is " << ((int)ei->d_cardinality_lem_k.get()-1) << std::endl;
            if( int_k+1 > ei->d_cardinality_lem_k.get() ){
                //add cardinality lemma
                Node dist = NodeManager::currentNM()->mkNode( kind::DISTINCT, cols[i] );
                std::vector< Node > vec_node;
                vec_node.push_back( dist );
                for( std::vector< Node >::iterator itr1 = cols[i].begin();
                      itr1 != cols[i].end(); ++itr1) {
                    Node len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, *itr1 );
                    if( len!=lr ){
                      Node len_eq_lr = NodeManager::currentNM()->mkNode( kind::EQUAL, lr, len );
                      vec_node.push_back( len_eq_lr );
                    }
                }
                Node antc = NodeManager::currentNM()->mkNode( kind::AND, vec_node );
                Node len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, cols[i][0] );
                Node cons = NodeManager::currentNM()->mkNode( kind::GT, len, k_node );
                Node lemma = NodeManager::currentNM()->mkNode( kind::IMPLIES, antc, cons );
				lemma = Rewriter::rewrite( lemma );
				if( lemma!=d_true ){
					Trace("strings-lemma") << "Strings cardinality lemma : " << lemma << std::endl;
					d_out->lemma(lemma);
				}
                ei->d_cardinality_lem_k.set( int_k+1 );
                return true;
            }
        }
    }
  }
  return false;
}

int TheoryStrings::gcd ( int a, int b ) {
  int c;
  while ( a != 0 ) {
     c = a; a = b%a;  b = c;
  }
  return b;
}

bool TheoryStrings::checkInductiveEquations() {
	if(d_ind_map1.size() == 0) return false;
	
    bool hasEq = false;
    Trace("strings-ind")  << "We are sat, with these inductive equations : " << std::endl;
    for( NodeListMap::const_iterator it = d_ind_map1.begin(); it != d_ind_map1.end(); ++it ){
        Node x = (*it).first;
        NodeList* lst1 = (*it).second;
        NodeList* lst2 = (*d_ind_map2.find(x)).second;
        NodeList* lste = (*d_ind_map_exp.find(x)).second;
        NodeList* lstl = (*d_ind_map_lemma.find(x)).second;
        NodeList::const_iterator i1 = lst1->begin();
        NodeList::const_iterator i2 = lst2->begin();
        NodeList::const_iterator ie = lste->begin();
        NodeList::const_iterator il = lstl->begin();
        while( i1!=lst1->end() ){
            Node y = *i1;
            Node z = *i2;
            if( il==lstl->end() ) {

				std::vector< Node > nf_y, nf_z, exp_y, exp_z;
				
				getFinalNormalForm( y, nf_y, exp_y);
				getFinalNormalForm( z, nf_z, exp_z);
				std::vector< Node > vec_empty;
				Node nexp_y = mkExplain( exp_y, vec_empty );
				Node nexp_z = mkExplain( exp_z, vec_empty );

				Node exp = *ie;

				exp = NodeManager::currentNM()->mkNode( kind::AND, exp, nexp_y, nexp_z );
				exp = Rewriter::rewrite( exp );

				Trace("strings-ind") << "Inductive equation : " << x << " = ( ";
				for( std::vector< Node >::const_iterator itr = nf_y.begin(); itr != nf_y.end(); ++itr) {
					Trace("strings-ind") << (*itr) << " ";
				}
				Trace("strings-ind") << " ++ ";
				for( std::vector< Node >::const_iterator itr = nf_z.begin(); itr != nf_z.end(); ++itr) {
					Trace("strings-ind") << (*itr) << " ";
				}
				Trace("strings-ind") << " )* ";
				for( std::vector< Node >::const_iterator itr = nf_y.begin(); itr != nf_y.end(); ++itr) {
					Trace("strings-ind") << (*itr) << " ";
				}
				Trace("strings-ind") << std::endl;
				Trace("strings-ind") << "Explanation is : " << exp << std::endl;
				std::vector< Node > nf_yz;
				nf_yz.insert( nf_yz.end(), nf_y.begin(), nf_y.end() );
				nf_yz.insert( nf_yz.end(), nf_z.begin(), nf_z.end() );
				std::vector< std::vector< Node > > cols;
				std::vector< Node > lts;
				seperateIntoCollections( nf_yz, cols, lts );
				Trace("strings-ind") << "This can be grouped into collections : " << std::endl;
				for( unsigned j=0; j<cols.size(); j++ ){
					Trace("strings-ind") << "  : ";
					for( unsigned k=0; k<cols[j].size(); k++ ){
						Trace("strings-ind") << cols[j][k] << " ";
					}
					Trace("strings-ind") << std::endl;
				}
				Trace("strings-ind") << std::endl;
				
                Trace("strings-ind") << "Add length lemma..." << std::endl;
				std::vector< int > co;
				co.push_back(0);
				for(unsigned int k=0; k<lts.size(); ++k) {
					if(lts[k].isConst() && lts[k].getType().isInteger()) {
						int len = lts[k].getConst<Rational>().getNumerator().toUnsignedInt();
						co[0] += cols[k].size() * len;
					} else {
						co.push_back( cols[k].size() );
					}
				}
				int g_co = co[0];
				for(unsigned k=1; k<co.size(); ++k) {
					g_co = gcd(g_co, co[k]);
				}
                Node lemma_len;
                // both constants
				Node len_x = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, x );
				Node sk = NodeManager::currentNM()->mkSkolem( "argsym_$$", NodeManager::currentNM()->integerType(), "created for length inductive lemma" );
				Node g_co_node = NodeManager::currentNM()->mkConst( CVC4::Rational(g_co) );
				Node sk_m_gcd = NodeManager::currentNM()->mkNode( kind::MULT, g_co_node, sk );
				Node len_y = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, y );
				Node sk_m_g_p_y =    NodeManager::currentNM()->mkNode( kind::PLUS, sk_m_gcd, len_y );
				lemma_len =     NodeManager::currentNM()->mkNode( kind::EQUAL, sk_m_g_p_y, len_x );
				//Node sk_geq_zero = NodeManager::currentNM()->mkNode( kind::GEQ, sk, d_zero );
				//lemma_len = NodeManager::currentNM()->mkNode( kind::AND, lemma_len, sk_geq_zero );
                lemma_len =     NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, lemma_len );
                Trace("strings-lemma") << "Strings: Add lemma " << lemma_len << std::endl;
                d_out->lemma(lemma_len);
                lstl->push_back( d_true );
                return true;
            }
            ++i1;
            ++i2;
            ++ie;
            ++il;
            hasEq = true;
        }
    }
    if( hasEq ){
        d_out->setIncomplete();
    }
  return false;
}

void TheoryStrings::getFinalNormalForm( Node n, std::vector< Node >& nf, std::vector< Node >& exp ) {
	if( n!=d_emptyString ){
		if( n.getKind()==kind::STRING_CONCAT ){
			for( unsigned i=0; i<n.getNumChildren(); i++ ){
				getFinalNormalForm( n[i], nf, exp );
			}
		}else{
			Trace("strings-debug") << "Get final normal form " << n << std::endl;
			Assert( d_equalityEngine.hasTerm( n ) );
			Node nr = d_equalityEngine.getRepresentative( n );
			EqcInfo *eqc_n = getOrMakeEqcInfo( nr, false );
			Node nc = eqc_n ? eqc_n->d_const_term.get() : Node::null();
			if( !nc.isNull() ){
				nf.push_back( nc );
				if( n!=nc ){
					exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n, nc ) );
				}
			}else{
				Assert( d_normal_forms.find( nr )!=d_normal_forms.end() );
				if( d_normal_forms[nr][0]==nr ){
					Assert( d_normal_forms[nr].size()==1 );
					nf.push_back( nr );
					if( n!=nr ){
						exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n, nr ) );
					}
				}else{
					for( unsigned i=0; i<d_normal_forms[nr].size(); i++ ){
						Assert( d_normal_forms[nr][i]!=nr );
						getFinalNormalForm( d_normal_forms[nr][i], nf, exp );
					}
					exp.insert( exp.end(), d_normal_forms_exp[nr].begin(), d_normal_forms_exp[nr].end() );
				}
			}
			Trace("strings-ind-nf") << "The final normal form of " << n << " is " << nf << std::endl;
		}
	}
}

void TheoryStrings::seperateIntoCollections( std::vector< Node >& n, std::vector< std::vector< Node > >& cols,
											 std::vector< Node >& lts ) {
  unsigned leqc_counter = 0;
  std::map< Node, unsigned > eqc_to_leqc;
  std::map< unsigned, Node > leqc_to_eqc;
  std::map< unsigned, std::vector< Node > > eqc_to_strings;
  for( unsigned i=0; i<n.size(); i++ ){
	Node eqc = n[i];
	Assert( d_equalityEngine.getRepresentative(eqc)==eqc );
	EqcInfo* ei = getOrMakeEqcInfo( eqc, false );
	Node lt = ei ? ei->d_length_term : Node::null();
	if( !lt.isNull() ){
	  lt = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt );
	  Node r = d_equalityEngine.getRepresentative( lt );
	  if( eqc_to_leqc.find( r )==eqc_to_leqc.end() ){
		eqc_to_leqc[r] = leqc_counter;
		leqc_to_eqc[leqc_counter] = r;
		leqc_counter++;
	  }
	  eqc_to_strings[ eqc_to_leqc[r] ].push_back( eqc );
	}else{
	  eqc_to_strings[leqc_counter].push_back( eqc );
	  leqc_counter++;
	}
  }
  for( std::map< unsigned, std::vector< Node > >::iterator it = eqc_to_strings.begin(); it != eqc_to_strings.end(); ++it ){
	std::vector< Node > vec;
	vec.insert( vec.end(), it->second.begin(), it->second.end() );

	lts.push_back( leqc_to_eqc[it->first] );
	cols.push_back( vec );
  }
}


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
