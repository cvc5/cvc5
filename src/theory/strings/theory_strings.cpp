/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "theory/theory_model.h"
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
	//d_var_lmin( c ),
	//d_var_lmax( c ),
	d_reg_exp_mem( c ),
	d_curr_cardinality( c, 0 )
{
    // The kinds we are treating as function application in congruence
    //d_equalityEngine.addFunctionKind(kind::STRING_IN_REGEXP);
    d_equalityEngine.addFunctionKind(kind::STRING_LENGTH);
    d_equalityEngine.addFunctionKind(kind::STRING_CONCAT);

    d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
    d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    d_true = NodeManager::currentNM()->mkConst( true );
    d_false = NodeManager::currentNM()->mkConst( false );

	d_regexp_incomplete = false;
	d_opt_regexp_gcd = true;
}

TheoryStrings::~TheoryStrings() {

}

Node TheoryStrings::getRepresentative( Node t ) {
	if( d_equalityEngine.hasTerm( t ) ){
		return d_equalityEngine.getRepresentative( t );
	}else{
		return t;
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

bool TheoryStrings::areDisequal( Node a, Node b ){
  if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

Node TheoryStrings::getLengthTerm( Node t ) {
	EqcInfo * ei = getOrMakeEqcInfo( t, false );
	Node length_term = ei ? ei->d_length_term : Node::null();
	if( length_term.isNull()) {
		//typically shouldnt be necessary
		length_term = t;
	}
	return length_term;
}

Node TheoryStrings::getLength( Node t ) {
	return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, getLengthTerm( t ) ) );
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

EqualityStatus TheoryStrings::getEqualityStatus(TNode a, TNode b) {
  if( d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b) ){
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b, false)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
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
  Debug("strings-explain") << "Explain " << literal << " " << d_conflict << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  unsigned ps = assumptions.size();
  std::vector< TNode > tassumptions;
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, tassumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, tassumptions);
  }
  for( unsigned i=0; i<tassumptions.size(); i++ ){
	if( std::find( assumptions.begin(), assumptions.end(), tassumptions[i] )==assumptions.end() ){
		assumptions.push_back( tassumptions[i] );
	}
  }
  Debug("strings-explain-debug") << "Explanation for " << literal << " was " << std::endl;
  for( unsigned i=ps; i<assumptions.size(); i++ ){
	Debug("strings-explain-debug") << "   " << assumptions[i] << std::endl;
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
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::presolve() {
	Trace("strings-presolve") << "TheoryStrings::Presolving : get fmf options " << (options::stringFMF() ? "true" : "false") << std::endl;
	Trace("strings-presolve") << "TheoryStrings::Presolving : get unroll depth options " << options::stringRegExpUnrollDepth() << std::endl;
	d_opt_fmf = options::stringFMF();
	d_regexp_max_depth = options::stringRegExpUnrollDepth();
	d_regexp_unroll_depth = options::stringRegExpUnrollDepth();
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
	getEquivalenceClasses( nodes );
	std::map< Node, Node > processed;
	std::vector< std::vector< Node > > col;
	std::vector< Node > lts;
	seperateByLength( nodes, col, lts );
	//step 1 : get all values for known lengths
	std::vector< Node > lts_values;
	std::map< unsigned, bool > values_used;
	for( unsigned i=0; i<col.size(); i++ ){
		Trace("strings-model") << "Checking length for {";
		for( unsigned j=0; j<col[i].size(); j++ ){
			if( j>0 ) Trace("strings-model") << ", ";
			Trace("strings-model") << col[i][j];
		}
		Trace("strings-model") << " } (length is " << lts[i] << ")" << std::endl;
		if( lts[i].isConst() ){
			lts_values.push_back( lts[i] );
			unsigned lvalue = lts[i].getConst<Rational>().getNumerator().toUnsignedInt();
			values_used[ lvalue ] = true;
		}else{
			//get value for lts[i];
			if( !lts[i].isNull() ){
				Node v = d_valuation.getModelValue(lts[i]);
				Trace("strings-model") << "Model value for " << lts[i] << " is " << v << std::endl;
				lts_values.push_back( v );
				unsigned lvalue =  v.getConst<Rational>().getNumerator().toUnsignedInt();
				values_used[ lvalue ] = true;
			}else{
				//Trace("strings-model-warn") << "No length for eqc " << col[i][0] << std::endl;
				//Assert( false );
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
				if( d_normal_forms[col[i][j]].size()==1 ){//&& d_normal_forms[col[i][j]][0]==col[i][j] ){
					pure_eq.push_back( col[i][j] );
				}
			}else{
				processed[col[i][j]] = cst;
			}
		}
		Trace("strings-model") << "have length " << lts_values[i] << std::endl;
		
		//assign a new length if necessary
		if( !pure_eq.empty() ){
			if( lts_values[i].isNull() ){
				unsigned lvalue = 0;
				while( values_used.find( lvalue )!=values_used.end() ){
					lvalue++;	
				}
				Trace("strings-model") << "*** Decide to make length of " << lvalue << std::endl;
				lts_values[i] = NodeManager::currentNM()->mkConst( Rational( lvalue ) );
				values_used[ lvalue ] = true;
			}
			Trace("strings-model") << "Need to assign values of length " << lts_values[i] << " to equivalence classes ";
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
				Trace("strings-model") << "*** Assigned constant " << c << " for " << pure_eq[j] << std::endl;
				processed[pure_eq[j]] = c;
				m->assertEquality( pure_eq[j], c, true );
			}
		}
	}
	Trace("strings-model") << "String Model : Finished." << std::endl;
	//step 4 : assign constants to all other equivalence classes
	for( unsigned i=0; i<nodes.size(); i++ ){
		if( processed.find( nodes[i] )==processed.end() ){
			Assert( d_normal_forms.find( nodes[i] )!=d_normal_forms.end() );
			Trace("strings-model") << "Construct model for " << nodes[i] << " based on normal form ";
			for( unsigned j=0; j<d_normal_forms[nodes[i]].size(); j++ ) {
				if( j>0 ) Trace("strings-model") << " ++ ";
				Trace("strings-model") << d_normal_forms[nodes[i]][j];
				Node r = getRepresentative( d_normal_forms[nodes[i]][j] );
				if( !r.isConst() && processed.find( r )==processed.end() ){
					Trace("strings-model") << "(UNPROCESSED)";
				}
			}
			Trace("strings-model") << std::endl;
			std::vector< Node > nc;
			for( unsigned j=0; j<d_normal_forms[nodes[i]].size(); j++ ) {
				Node r = getRepresentative( d_normal_forms[nodes[i]][j] );
				Assert( r.isConst() || processed.find( r )!=processed.end() );
				nc.push_back(r.isConst() ? r : processed[r]);
			}
			Node cc = mkConcat( nc );
			Assert( cc.getKind()==kind::CONST_STRING );
			Trace("strings-model") << "*** Determined constant " << cc << " for " << nodes[i] << std::endl;
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
    //d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
    if(n.getKind() == kind::VARIABLE || n.getKind()==kind::SKOLEM) {
	  if( std::find( d_length_intro_vars.begin(), d_length_intro_vars.end(), n )==d_length_intro_vars.end() ){
		  Node n_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n);
		  Node n_len_eq_z = n_len.eqNode( d_zero );
		  Node n_len_geq_zero = NodeManager::currentNM()->mkNode( kind::OR, n_len_eq_z,
									NodeManager::currentNM()->mkNode( kind::GT, n_len, d_zero) );
		  Trace("strings-lemma") << "Strings::Lemma LENGTH geq 0 : " << n_len_geq_zero << std::endl;
		  d_out->lemma(n_len_geq_zero);
		  d_out->requirePhase( n_len_eq_z, true );
	  }
	  // FMF
	  if( n.getKind() == kind::VARIABLE ) {//options::stringFMF() && 
		  if( std::find(d_in_vars.begin(), d_in_vars.end(), n) == d_in_vars.end() ) {
			  d_in_vars.push_back( n );
		  }
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

void TheoryStrings::check(Effort e) {
  //Assert( d_pending.empty() );

  bool polarity;
  TNode atom;

  if( !done() && !hasTerm( d_emptyString ) ){
	 preRegisterTerm( d_emptyString );
  }

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
	//must record string in regular expressions
	if ( atom.getKind() == kind::STRING_IN_REGEXP ) {
		d_reg_exp_mem.push_back( assertion );
	}else if (atom.getKind() == kind::EQUAL) {
		d_equalityEngine.assertEquality(atom, polarity, fact);
    } else {
		d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
  }
  doPendingFacts();


  bool addedLemma = false;
  if( e == EFFORT_FULL && !d_conflict ) {
      addedLemma = checkLengths();
	  Trace("strings-process") << "Done check (constant) lengths, addedLemma = " << addedLemma << ", d_conflict = " << d_conflict << std::endl;
	  if( !addedLemma ){
		  addedLemma = checkNormalForms();
		  Trace("strings-process") << "Done check normal forms, addedLemma = " << addedLemma << ", d_conflict = " << d_conflict << std::endl;
		  if(!d_conflict && !addedLemma) {
			  addedLemma = checkLengthsEqc();
			  Trace("strings-process") << "Done check lengths, addedLemma = " << addedLemma << ", d_conflict = " << d_conflict << std::endl;
			  if(!d_conflict && !addedLemma) {
				  addedLemma = checkCardinality();
				  Trace("strings-process") << "Done check cardinality, addedLemma = " << addedLemma << ", d_conflict = " << d_conflict << std::endl;
				  if( !d_conflict && !addedLemma ){
					addedLemma = checkMemberships();
					Trace("strings-process") << "Done check membership constraints, addedLemma = " << addedLemma << ", d_conflict = " << d_conflict << std::endl;
				  }
			  }
		  }
	  }
  }
  Trace("strings-check") << "Theory of strings, done check : " << e << std::endl;
  Trace("strings-process") << "Theory of strings, done check : " << e << std::endl;
  Assert( d_pending.empty() );
  Assert( d_lemma_cache.empty() );
}

TheoryStrings::EqcInfo::EqcInfo(  context::Context* c ) : d_const_term(c), d_length_term(c), d_cardinality_lem_k(c), d_normalized_length(c) {

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
  if( !d_conflict ){
	  Trace("strings-conflict-debug") << "Making conflict..." << std::endl;
	  d_conflict = true;
	  Node conflictNode;
	  if (a.getKind() == kind::CONST_BOOLEAN) {
		conflictNode = explain( a.iffNode(b) );
	  } else {
		conflictNode = explain( a.eqNode(b) );
	  }
	  Trace("strings-conflict") << "CONFLICT: Eq engine conflict : " << conflictNode << std::endl;
	  d_out->conflict( conflictNode );
  }
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
		if( !e2->d_normalized_length.get().isNull() ){
			e1->d_normalized_length.set( e2->d_normalized_length );
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
                    //apply the rule length(n[0])==0 => n[0] == ""
                    Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, n[0], d_emptyString );
                    d_pending.push_back( eq );
                    Node eq_exp = NodeManager::currentNM()->mkNode( kind::EQUAL, n, d_zero );
                    d_pending_exp[eq] = eq_exp;
                    Trace("strings-infer") << "Strings : Infer Empty : " << eq << " from " << eq_exp << std::endl;
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
		//Assert( d_equalityEngine.hasTerm( atom[0] ) );
		//Assert( d_equalityEngine.hasTerm( atom[1] ) );
		for( unsigned j=0; j<2; j++ ){
			if( !d_equalityEngine.hasTerm( atom[j] ) ){
				d_equalityEngine.addTerm( atom[j] );
			}
		}
		d_equalityEngine.assertEquality( atom, polarity, exp );
      }else{
        d_equalityEngine.assertPredicate( atom, polarity, exp );
      }
    i++;
  }
  d_pending.clear();
  d_pending_exp.clear();
}
void TheoryStrings::doPendingLemmas() {
  if( !d_conflict && !d_lemma_cache.empty() ){
	  for( unsigned i=0; i<d_lemma_cache.size(); i++ ){
		  Trace("strings-pending") << "Process pending lemma : " << d_lemma_cache[i] << std::endl;
		  d_out->lemma( d_lemma_cache[i] );
	  }
	  for( std::map< Node, bool >::iterator it = d_pending_req_phase.begin(); it != d_pending_req_phase.end(); ++it ){
		Trace("strings-pending") << "Require phase : " << it->first << ", polarity = " << it->second << std::endl;
		d_out->requirePhase( it->first, it->second );
	  }
  }
  d_lemma_cache.clear();
  d_pending_req_phase.clear();
}

bool TheoryStrings::getNormalForms(Node &eqc, std::vector< Node > & visited, std::vector< Node > & nf,
    std::vector< std::vector< Node > > &normal_forms,  std::vector< std::vector< Node > > &normal_forms_exp, std::vector< Node > &normal_form_src) {
	Trace("strings-process-debug") << "Get normal forms " << eqc << std::endl;
    // EqcItr
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ) {
        Node n = (*eqc_i);
        if( n.getKind() == kind::CONST_STRING || n.getKind() == kind::STRING_CONCAT ) {
			Trace("strings-process-debug") << "Get Normal Form : Process term " << n << " in eqc " << eqc << std::endl;
            std::vector<Node> nf_n;
            std::vector<Node> nf_exp_n;
			bool result = true;
            if( n.getKind() == kind::CONST_STRING  ){
                if( n!=d_emptyString ) {
                    nf_n.push_back( n );
                }
            } else if( n.getKind() == kind::STRING_CONCAT ) {
                for( unsigned i=0; i<n.getNumChildren(); i++ ) {
                    Node nr = d_equalityEngine.getRepresentative( n[i] );
                    std::vector< Node > nf_temp;
                    std::vector< Node > nf_exp_temp;
                    Trace("strings-process-debug") << "Normalizing subterm " << n[i] << " = "  << nr << std::endl;
                    bool nresult = normalizeEquivalenceClass( nr, visited, nf_temp, nf_exp_temp );
                    if( d_conflict || !d_pending.empty() || !d_lemma_cache.empty() ) {
                        return true;
                    }
					//successfully computed normal form
					if( nf.size()!=1 || nf[0]!=d_emptyString ) {
						for( unsigned r=0; r<nf_temp.size(); r++ ) {
							if( nresult && nf_temp[r].getKind()==kind::STRING_CONCAT ){
								Trace("strings-error") << "Strings::Error: From eqc = " << eqc << ", " << n << " index " << i << ", bad normal form : ";
								for( unsigned rr=0; rr<nf_temp.size(); rr++ ) {
									Trace("strings-error") << nf_temp[rr] << " ";
								}
								Trace("strings-error") << std::endl;
							}
							Assert( !nresult || nf_temp[r].getKind()!=kind::STRING_CONCAT );
						}
						nf_n.insert( nf_n.end(), nf_temp.begin(), nf_temp.end() );
					}
					nf_exp_n.insert( nf_exp_n.end(), nf_exp_temp.begin(), nf_exp_temp.end() );
					if( nr!=n[i] ) {
						nf_exp_n.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n[i], nr ) );
					}
					if( !nresult ){
						//Trace("strings-process-debug") << "....Caused already asserted 
						for( unsigned j=i+1; j<n.getNumChildren(); j++ ){
							if( !areEqual( n[j], d_emptyString ) ){
								nf_n.push_back( n[j] );
							}
						}
						if( nf_n.size()>1 ){
							result = false;
							break;
						}
					}
                }
            }
			if( nf_n.size()>1 || ( nf_n.size()==1 && nf_n[0].getKind()==kind::CONST_STRING ) ){
				if( nf_n.size()>1 ){
					Trace("strings-process-debug") << "Check for component lemmas for normal form "; 
					printConcat(nf_n,"strings-process-debug");
					Trace("strings-process-debug") << "..." << std::endl;
					for( unsigned i=0; i<nf_n.size(); i++ ){
						//if a component is equal to whole,
						if( areEqual( nf_n[i], n ) ){
							//all others must be empty
							std::vector< Node > ant;
							if( nf_n[i]!=n ){
								ant.push_back( nf_n[i].eqNode( n ) );
							}
							ant.insert( ant.end(), nf_exp_n.begin(), nf_exp_n.end() );
							std::vector< Node > cc;
							for( unsigned j=0; j<nf_n.size(); j++ ){
								if( i!=j ){
									cc.push_back( nf_n[j].eqNode( d_emptyString ) );
								}
							}
							std::vector< Node > empty_vec;
							Node conc = cc.size()==1 ? cc[0] : NodeManager::currentNM()->mkNode( kind::AND, cc );
							sendLemma( mkExplain( ant ), conc, "Component" );
							return true;
						}
					}
				}
				if( !result ){
					//we have a normal form that will cause a component lemma at a higher level
					normal_forms.clear();
					normal_forms_exp.clear();
					normal_form_src.clear();
				}
				normal_forms.push_back(nf_n);
				normal_forms_exp.push_back(nf_exp_n);
				normal_form_src.push_back(n);
				if( !result ){
					return false;
				}
			}else{
				Node nn = nf_n.size()==0 ? d_emptyString : nf_n[0];
				//Assert( areEqual( nf_n[0], eqc ) );
				if( !areEqual( nn, eqc ) ){
					std::vector< Node > ant;
					ant.insert( ant.end(), nf_exp_n.begin(), nf_exp_n.end() );
					ant.push_back( n.eqNode( eqc ) );
					Node conc = nn.eqNode( eqc );
					sendLemma( mkExplain( ant ), conc, "Trivial Equal Normal Form" );
					return true;
				}
			}
        }
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
	return true;
}

bool TheoryStrings::detectLoop( std::vector< std::vector< Node > > &normal_forms,
								int i, int j, int index_i, int index_j, 
								int &loop_in_i, int &loop_in_j) {
	int has_loop[2] = { -1, -1 };
	if( options::stringLB() != 2 ) {
		for( unsigned r=0; r<2; r++ ) {
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
	}
	if( has_loop[0]!=-1 || has_loop[1]!=-1 ) {
		loop_in_i = has_loop[0];
		loop_in_j = has_loop[1];
		return true;
	} else {
		return false;
	}
}
//xs(zy)=t(yz)xr
bool TheoryStrings::processLoop(std::vector< Node > &antec, 
								std::vector< std::vector< Node > > &normal_forms,
								std::vector< Node > &normal_form_src,
								int i, int j, int loop_n_index, int other_n_index,
								int loop_index, int index, int other_index) {
	Node conc;
	Trace("strings-loop") << "Detected possible loop for " << normal_forms[loop_n_index][loop_index] << std::endl;
	Trace("strings-loop") << " ... (X)= " << normal_forms[other_n_index][other_index] << std::endl;
	
	Trace("strings-loop") << " ... T(Y.Z)= ";
	std::vector< Node > vec_t;
	for(int lp=index; lp<loop_index; ++lp) {
		if(lp != index) Trace("strings-loop") << " ++ ";
		Trace("strings-loop") << normal_forms[loop_n_index][lp];
		vec_t.push_back( normal_forms[loop_n_index][lp] );
	}
	Node t_yz = mkConcat( vec_t );
	Trace("strings-loop") << " (" << t_yz << ")" << std::endl;
	Trace("strings-loop") << " ... S(Z.Y)= ";
	std::vector< Node > vec_s;
	for(int lp=other_index+1; lp<(int)normal_forms[other_n_index].size(); ++lp) {
		if(lp != other_index+1) Trace("strings-loop") << " ++ ";
		Trace("strings-loop") << normal_forms[other_n_index][lp];
		vec_s.push_back( normal_forms[other_n_index][lp] );
	}
	Node s_zy = mkConcat( vec_s );
	Trace("strings-loop") << " (" << s_zy << ")" << std::endl;
	Trace("strings-loop") << " ... R= ";
	std::vector< Node > vec_r;
	for(int lp=loop_index+1; lp<(int)normal_forms[loop_n_index].size(); ++lp) {
		if(lp != loop_index+1) Trace("strings-loop") << " ++ ";
		Trace("strings-loop") << normal_forms[loop_n_index][lp];
		vec_r.push_back( normal_forms[loop_n_index][lp] );
	}
	Node r = mkConcat( vec_r );
	Trace("strings-loop") << " (" << r << ")" << std::endl;

	//Trace("strings-loop") << "Lemma Cache: " << normal_form_src[i] << " vs " << normal_form_src[j] << std::endl;
	//TODO: can be more general
	if( s_zy.isConst() && r.isConst() && r != d_emptyString) {
		int c;
		bool flag = true;
		if(s_zy.getConst<String>().tailcmp( r.getConst<String>(), c ) ) {
			if(c >= 0) {
				s_zy = NodeManager::currentNM()->mkConst( s_zy.getConst<String>().substr(0, c) );
				r = d_emptyString;
				vec_r.clear();
				Trace("strings-loop") << "Strings::Loop: Refactor S(Z.Y)= " << s_zy << ", c=" << c << std::endl;
				flag = false;
			}
		}
		if(flag) {
			Trace("strings-loop") << "Strings::Loop: tails are different." << std::endl;
			Node ant = mkExplain( antec );
			sendLemma( ant, conc, "Conflict" );
			return true;
		}
	}

	//require that x is non-empty
	if( !areDisequal( normal_forms[loop_n_index][loop_index], d_emptyString ) ){
		//try to make normal_forms[loop_n_index][loop_index] equal to empty to avoid loop
		sendSplit( normal_forms[loop_n_index][loop_index], d_emptyString, "Loop Empty x" );
	} else if( !areDisequal( t_yz, d_emptyString ) && t_yz.getKind()!=kind::CONST_STRING  ) {
		//try to make normal_forms[loop_n_index][loop_index] equal to empty to avoid loop
		sendSplit( t_yz, d_emptyString, "Loop Empty yz" );
	} else {
		//need to break
		antec.push_back( normal_forms[loop_n_index][loop_index].eqNode( d_emptyString ).negate() );
		if( t_yz.getKind()!=kind::CONST_STRING ) {
			antec.push_back( t_yz.eqNode( d_emptyString ).negate() );
		}
		Node ant = mkExplain( antec );
		if(d_loop_antec.find(ant) == d_loop_antec.end()) {
			d_loop_antec[ant] = true;

			Node str_in_re;
			if( s_zy == t_yz &&
				r == d_emptyString &&
				s_zy.isConst() &&
				s_zy.getConst<String>().isRepeated()
				) {
				Node rep_c = NodeManager::currentNM()->mkConst( s_zy.getConst<String>().substr(0, 1) );
				Trace("strings-loop") << "Special case (X)=" << normal_forms[other_n_index][other_index] << " " << std::endl;
				Trace("strings-loop") << "... (C)=" << rep_c << " " << std::endl;
				//special case
				str_in_re = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, normal_forms[other_n_index][other_index], 
							  NodeManager::currentNM()->mkNode( kind::REGEXP_STAR,
								NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, rep_c ) ) );
				conc = str_in_re;
			} else {
				Trace("strings-loop") << "Strings::Loop: Normal Splitting." << std::endl;
				//right
				Node sk_w= NodeManager::currentNM()->mkSkolem( "w_loop_$$", normal_forms[other_n_index][other_index].getType(), "created for loop detection split" );
				Node sk_y= NodeManager::currentNM()->mkSkolem( "y_loop_$$", normal_forms[other_n_index][other_index].getType(), "created for loop detection split" );
				Node sk_z= NodeManager::currentNM()->mkSkolem( "z_loop_$$", normal_forms[other_n_index][other_index].getType(), "created for loop detection split" );
				//t1 * ... * tn = y * z
				Node conc1 = t_yz.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk_y, sk_z ) );
				// s1 * ... * sk = z * y * r
				vec_r.insert(vec_r.begin(), sk_y);
				vec_r.insert(vec_r.begin(), sk_z);
				Node conc2 = s_zy.eqNode( mkConcat( vec_r ) );
				Node conc3 = normal_forms[other_n_index][other_index].eqNode( mkConcat( sk_y, sk_w ) );
				str_in_re = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, sk_w, 
								NodeManager::currentNM()->mkNode( kind::REGEXP_STAR,
									NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, mkConcat( sk_z, sk_y ) ) ) );
				
				//Node sk_y_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk_y );
				//Node zz_imp_yz = NodeManager::currentNM()->mkNode( kind::IMPLIES, sk_z.eqNode(d_emptyString), sk_y.eqNode(d_emptyString));
				
				std::vector< Node > vec_conc;
				vec_conc.push_back(conc1); vec_conc.push_back(conc2); vec_conc.push_back(conc3);
				vec_conc.push_back(str_in_re);
				vec_conc.push_back(sk_y.eqNode(d_emptyString).negate());
				conc = NodeManager::currentNM()->mkNode( kind::AND, vec_conc );//, len_x_gt_len_y
			} // normal case

			//set its antecedant to ant, to say when it is relevant
			d_reg_exp_ant[str_in_re] = ant;
			//unroll the str in re constraint once
			unrollStar( str_in_re );
			sendLemma( ant, conc, "LOOP-BREAK" );

			//we will be done
			addNormalFormPair( normal_form_src[i], normal_form_src[j] );
		} else {
			Trace("strings-loop") << "Strings::Loop: loop lemma for " << ant << " has already added." << std::endl;
			addNormalFormPair( normal_form_src[i], normal_form_src[j] );
			return false;
		}
	}
	return true;
}
bool TheoryStrings::processNEqc(std::vector< std::vector< Node > > &normal_forms,
								std::vector< std::vector< Node > > &normal_forms_exp,
								std::vector< Node > &normal_form_src) {
	bool flag_lb = false;
	std::vector< Node > c_lb_exp;
	int c_i, c_j, c_loop_n_index, c_other_n_index, c_loop_index, c_index, c_other_index;
	for(unsigned i=0; i<normal_forms.size()-1; i++) {
		//unify each normalform[j] with normal_forms[i]
		for( unsigned j=i+1; j<normal_forms.size(); j++ ) {
			Trace("strings-solve") << "Strings: Process normal form #" << i << " against #" << j << "..." << std::endl;
			if( isNormalFormPair( normal_form_src[i], normal_form_src[j] ) ) {
				Trace("strings-solve") << "Strings: Already cached." << std::endl;
			} else {
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
						if( index_i==normal_forms[i].size() && index_j==normal_forms[j].size() ) {
							//we're done
							addNormalFormPair( normal_form_src[i], normal_form_src[j] );
						} else {
							//the remainder must be empty
							unsigned k = index_i==normal_forms[i].size() ? j : i;
							unsigned index_k = index_i==normal_forms[i].size() ? index_j : index_i;
							Node eq_exp;
							if( curr_exp.empty() ) {
								eq_exp = d_true;
							} else if( curr_exp.size() == 1 ) {
								eq_exp = curr_exp[0];
							} else {
								eq_exp = NodeManager::currentNM()->mkNode( kind::AND, curr_exp );
							}
							while(!d_conflict && index_k<normal_forms[k].size()) {
								//can infer that this string must be empty
								Node eq = normal_forms[k][index_k].eqNode( d_emptyString );
								Trace("strings-lemma") << "Strings: Infer " << eq << " from " << eq_exp << std::endl;
								Assert( !areEqual( d_emptyString, normal_forms[k][index_k] ) );
								d_pending.push_back( eq );
								d_pending_exp[eq] = eq_exp;
								d_infer.push_back(eq);
								d_infer_exp.push_back(eq_exp);
								index_k++;
							}
						}
					} else {
						Trace("strings-solve-debug") << "Process " << normal_forms[i][index_i] << " ... " << normal_forms[j][index_j] << std::endl;
						if(areEqual(normal_forms[i][index_i], normal_forms[j][index_j])) {
							Trace("strings-solve-debug") << "Case 1 : strings are equal" << std::endl;
							//terms are equal, continue
							if( normal_forms[i][index_i]!=normal_forms[j][index_j] ) {
								Node eq = normal_forms[i][index_i].eqNode(normal_forms[j][index_j]);
								Trace("strings-solve-debug") << "Add to explanation : " << eq << std::endl;
								curr_exp.push_back(eq);
							}
							index_j++;
							index_i++;
							success = true;
						} else {
							Node length_term_i = getLength( normal_forms[i][index_i] );
							Node length_term_j = getLength( normal_forms[j][index_j] );
							//check  length(normal_forms[i][index]) == length(normal_forms[j][index])
							if( !areDisequal(length_term_i, length_term_j) &&
								!areEqual(length_term_i, length_term_j) &&
								normal_forms[i][index_i].getKind()!=kind::CONST_STRING && 
								normal_forms[j][index_j].getKind()!=kind::CONST_STRING ) {
								//length terms are equal, merge equivalence classes if not already done so
								Node length_eq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j );
								Trace("strings-solve-debug") << "Case 2.1 : string lengths neither equal nor disequal" << std::endl;
								//try to make the lengths equal via splitting on demand
								sendSplit( length_term_i, length_term_j, "Length" );
								length_eq = Rewriter::rewrite( length_eq  );
								d_pending_req_phase[ length_eq ] = true;
								return true;
							} else if( areEqual(length_term_i, length_term_j) ) {
								Trace("strings-solve-debug") << "Case 2.2 : string lengths are equal" << std::endl;
								Node eq = normal_forms[i][index_i].eqNode( normal_forms[j][index_j] );
								Node length_eq = length_term_i.eqNode( length_term_j );
								std::vector< Node > temp_exp;
								temp_exp.insert(temp_exp.end(), curr_exp.begin(), curr_exp.end() );
								temp_exp.push_back(length_eq);
								Node eq_exp = temp_exp.empty() ? d_true :
												temp_exp.size() == 1 ? temp_exp[0] : NodeManager::currentNM()->mkNode( kind::AND, temp_exp );
								Trace("strings-lemma") << "Strings: Infer " << eq << " from " << eq_exp << std::endl;
								d_pending.push_back( eq );
								d_pending_exp[eq] = eq_exp;
								d_infer.push_back(eq);
								d_infer_exp.push_back(eq_exp);
								return true;
							} else if(( normal_forms[i][index_i].getKind()!=kind::CONST_STRING && index_i==normal_forms[i].size()-1 ) || 
									  ( normal_forms[j][index_j].getKind()!=kind::CONST_STRING && index_j==normal_forms[j].size()-1 ) ) {
								Trace("strings-solve-debug") << "Case 3 : at endpoint" << std::endl;
								Node conc;
								std::vector< Node > antec;
								antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
								std::vector< Node > eqn;
								for( unsigned r=0; r<2; r++ ) {
									int index_k = r==0 ? index_i : index_j;
									int k = r==0 ? i : j;
									std::vector< Node > eqnc;
									for( unsigned index_l=index_k; index_l<normal_forms[k].size(); index_l++ ){
										eqnc.push_back( normal_forms[k][index_l] );
									}
									eqn.push_back( mkConcat( eqnc ) );
								}
								if( areEqual( eqn[0], eqn[1] ) ) {
									addNormalFormPair( normal_form_src[i], normal_form_src[j] );
								} else {
									conc = eqn[0].eqNode( eqn[1] );
									Node ant = mkExplain( antec );
									sendLemma( ant, conc, "ENDPOINT" );
									return true;
								}
							} else {
								Trace("strings-solve-debug") << "Case 4 : must compare strings" << std::endl;
								int loop_in_i = -1;
								int loop_in_j = -1;
								if(detectLoop(normal_forms, i, j, index_i, index_j, loop_in_i, loop_in_j)) {
									if(!flag_lb) {
										c_i = i;
										c_j = j;
										c_loop_n_index = loop_in_i!=-1 ? i : j;
										c_other_n_index = loop_in_i!=-1 ? j : i;
										c_loop_index = loop_in_i!=-1 ? loop_in_i : loop_in_j;
										c_index = loop_in_i!=-1 ? index_i : index_j;
										c_other_index = loop_in_i!=-1 ? index_j : index_i;

										c_lb_exp = curr_exp;

										if(options::stringLB() == 0) {
											flag_lb = true;
										} else {
											if(processLoop(c_lb_exp, normal_forms, normal_form_src, 
												c_i, c_j, c_loop_n_index, c_other_n_index, c_loop_index, c_index, c_other_index)) {
												return true;
											}
										}
									}
								} else {
									Node conc;
									std::vector< Node > antec;
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
												Node ant = mkExplain( antec );
												sendLemma( ant, conc, "Conflict" );
												return true;
											}
										} else {
											Assert( other_str.getKind()!=kind::STRING_CONCAT );
											antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
											Node firstChar = const_str.getConst<String>().size() == 1 ? const_str :
												NodeManager::currentNM()->mkConst( const_str.getConst<String>().substr(0, 1) );
											//split the string
											Node eq1 = Rewriter::rewrite( other_str.eqNode( d_emptyString ) );
											Node eq2 = mkSplitEq( "c_spt_$$", "created for v/c split", other_str, firstChar, false );
											d_pending_req_phase[ eq1 ] = true;
											conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );
											Trace("strings-solve-debug") << "Break normal form constant/variable " << std::endl;

											Node ant = mkExplain( antec );
											sendLemma( ant, conc, "CST-SPLIT" );
											return true;
										}
									} else {
										std::vector< Node > antec_new_lits;
										antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );

										Node ldeq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ).negate();
										if( d_equalityEngine.areDisequal( length_term_i, length_term_j, true ) ){
											antec.push_back( ldeq );
										}else{
											antec_new_lits.push_back(ldeq);
										}

										//x!=e /\ y!=e
										for(unsigned xory=0; xory<2; xory++) {
											Node x = xory==0 ? normal_forms[i][index_i] : normal_forms[j][index_j];
											Node xgtz = x.eqNode( d_emptyString ).negate();
											if( areDisequal( x, d_emptyString ) ) {
												antec.push_back( xgtz );
											} else {
												antec_new_lits.push_back( xgtz );
											}
										}

										//Node sk = NodeManager::currentNM()->mkSkolem( "v_spt_$$", normal_forms[i][index_i].getType(), "created for v/v split" );
										//Node eq1 = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[i][index_i],
										//			NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, normal_forms[j][index_j], sk ) ) );
										//Node eq2 = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[j][index_j],
										//			NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, normal_forms[i][index_i], sk ) ) );
										Node eq1 = mkSplitEq( "v_spt_l_$$", "created for v/v split", normal_forms[i][index_i], normal_forms[j][index_j], true );
										Node eq2 = mkSplitEq( "v_spt_r_$$", "created for v/v split", normal_forms[j][index_j], normal_forms[i][index_i], true );
										conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );

										Node ant = mkExplain( antec, antec_new_lits );
										sendLemma( ant, conc, "VAR-SPLIT" );
										return true;
									}
								}
							}
						}
					}
				} while(success);
			}
		}
		if(!flag_lb) {
			return false;
		}
	}
	if(flag_lb) {
		if(processLoop(c_lb_exp, normal_forms, normal_form_src, 
			c_i, c_j, c_loop_n_index, c_other_n_index, c_loop_index, c_index, c_other_index)) {
			return true;
		}
	}

	return false;
}

//nf_exp is conjunction
bool TheoryStrings::normalizeEquivalenceClass( Node eqc, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp ) {
    Trace("strings-process") << "Process equivalence class " << eqc << std::endl;
    if( std::find( visited.begin(), visited.end(), eqc )!=visited.end() ){
		getConcatVec( eqc, nf );
        Trace("strings-process") << "Return process equivalence class " << eqc << " : already visited." << std::endl;
		return false;
    } else if( areEqual( eqc, d_emptyString ) ) {
		eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
		while( !eqc_i.isFinished() ) {
			Node n = (*eqc_i);
			if( n.getKind()==kind::STRING_CONCAT ){
				for( unsigned i=0; i<n.getNumChildren(); i++ ){
					if( !areEqual( n[i], d_emptyString ) ){
						sendLemma( n.eqNode( d_emptyString ), n[i].eqNode( d_emptyString ), "CYCLE" );
					}
				}
			}
			++eqc_i;
		}
        //do nothing
        Trace("strings-process") << "Return process equivalence class " << eqc << " : empty." << std::endl;
		d_normal_forms_base[eqc] = d_emptyString;
		d_normal_forms[eqc].clear();
		d_normal_forms_exp[eqc].clear();
		return true;
    } else {
        visited.push_back( eqc );
		bool result;
        if(d_normal_forms.find(eqc)==d_normal_forms.end() ) {
            //phi => t = s1 * ... * sn
            // normal form for each non-variable term in this eqc (s1...sn)
            std::vector< std::vector< Node > > normal_forms;
            // explanation for each normal form (phi)
            std::vector< std::vector< Node > > normal_forms_exp;
            // record terms for each normal form (t)
            std::vector< Node > normal_form_src;
            //Get Normal Forms
            result = getNormalForms(eqc, visited, nf, normal_forms, normal_forms_exp, normal_form_src);
            if( d_conflict || !d_pending.empty() || !d_lemma_cache.empty() ) {
                return true;
            } else if( result ) {
				if(processNEqc(normal_forms, normal_forms_exp, normal_form_src)) {
					return true;
				}
			}

            //construct the normal form
            if( normal_forms.empty() ){
                Trace("strings-solve-debug2") << "construct the normal form" << std::endl;
				getConcatVec( eqc, nf );
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

    	    d_normal_forms_base[eqc] = normal_form_src.empty() ? eqc : normal_form_src[0];
            d_normal_forms[eqc].insert( d_normal_forms[eqc].end(), nf.begin(), nf.end() );
            d_normal_forms_exp[eqc].insert( d_normal_forms_exp[eqc].end(), nf_exp.begin(), nf_exp.end() );
            Trace("strings-process") << "Return process equivalence class " << eqc << " : returned, size = " << nf.size() << std::endl;
        }else{
            Trace("strings-process") << "Return process equivalence class " << eqc << " : already computed, size = " << d_normal_forms[eqc].size() << std::endl;
            nf.insert( nf.end(), d_normal_forms[eqc].begin(), d_normal_forms[eqc].end() );
            nf_exp.insert( nf_exp.end(), d_normal_forms_exp[eqc].begin(), d_normal_forms_exp[eqc].end() );
			result = true;
        }
        visited.pop_back();
		return result;
    }
}

bool TheoryStrings::normalizeDisequality( Node ni, Node nj ) {
	//Assert( areDisequal( ni, nj ) );
	if( d_normal_forms[ni].size()>1 || d_normal_forms[nj].size()>1 ){
		std::vector< Node > nfi;
		nfi.insert( nfi.end(), d_normal_forms[ni].begin(), d_normal_forms[ni].end() );
		std::vector< Node > nfj;
		nfj.insert( nfj.end(), d_normal_forms[nj].begin(), d_normal_forms[nj].end() );

		unsigned index = 0;
		while( index<nfi.size() || index<nfj.size() ){
			if( index>=nfi.size() || index>=nfj.size() ){
				std::vector< Node > ant;
				//we have a conflict : because the lengths are equal, the remainder needs to be empty, which will lead to a conflict
				Node lni = getLength( ni );
				Node lnj = getLength( nj );
				ant.push_back( lni.eqNode( lnj ) );
				ant.push_back( getLengthTerm( ni ).eqNode( d_normal_forms_base[ni] ) );
				ant.push_back( getLengthTerm( nj ).eqNode( d_normal_forms_base[nj] ) );
				ant.insert( ant.end(), d_normal_forms_exp[ni].begin(), d_normal_forms_exp[ni].end() );
				ant.insert( ant.end(), d_normal_forms_exp[nj].begin(), d_normal_forms_exp[nj].end() );
				std::vector< Node > cc;
				std::vector< Node >& nfk = index>=nfi.size() ? nfj : nfi;
				for( unsigned index_k=index; index_k<nfk.size(); index_k++ ){
					cc.push_back( nfk[index_k].eqNode( d_emptyString ) );
				}
				Node conc = cc.size()==1 ? cc[0] : NodeManager::currentNM()->mkNode( kind::AND, cc );
				conc = Rewriter::rewrite( conc );
				sendLemma(mkExplain( ant ), conc, "Disequality Normalize Empty");
				return true;
			}else{
				Node i = nfi[index];
				Node j = nfj[index];
				Trace("strings-solve-debug")  << "...Processing " << i << " " << j << std::endl;
				if( !areEqual( i, j ) ) {
					if( i.getKind()==kind::CONST_STRING && j.getKind()==kind::CONST_STRING ){
						unsigned int len_short = i.getConst<String>().size() < j.getConst<String>().size() ? i.getConst<String>().size() : j.getConst<String>().size();
						String si = i.getConst<String>().substr(0, len_short);
						String sj = j.getConst<String>().substr(0, len_short);
						if(si == sj) {
							if( i.getConst<String>().size() < j.getConst<String>().size() ) {
								Node remainderStr = NodeManager::currentNM()->mkConst( j.getConst<String>().substr(len_short) );
								Trace("strings-solve-debug-test") << "Break normal form of " << nfj[index] << " into " << nfi[index] << ", " << remainderStr << std::endl;
								nfj.insert( nfj.begin() + index + 1, remainderStr );
								nfj[index] = nfi[index];
							} else {
								Node remainderStr = NodeManager::currentNM()->mkConst( i.getConst<String>().substr(len_short) );
								Trace("strings-solve-debug-test") << "Break normal form of " << nfi[index] << " into " << nfj[index] << ", " << remainderStr << std::endl;
								nfi.insert( nfi.begin() + index + 1, remainderStr );
								nfi[index] = nfj[index];
							}
						} else {
							//conflict
							return false;
						}
					}else{
						Node li = getLength( i );
						Node lj = getLength( j );
						if( areDisequal(li, lj) ){
							Trace("strings-solve") << "Case 2 : add lemma " << std::endl;
							//must add lemma
							std::vector< Node > antec;
							std::vector< Node > antec_new_lits;
							antec.insert( antec.end(), d_normal_forms_exp[ni].begin(), d_normal_forms_exp[ni].end() );
							antec.insert( antec.end(), d_normal_forms_exp[nj].begin(), d_normal_forms_exp[nj].end() );
							antec.push_back( ni.eqNode( nj ).negate() );
							antec_new_lits.push_back( li.eqNode( lj ).negate() );
							std::vector< Node > conc;
							Node sk1 = NodeManager::currentNM()->mkSkolem( "x_dsplit_$$", ni.getType(), "created for disequality normalization" );
							Node sk2 = NodeManager::currentNM()->mkSkolem( "y_dsplit_$$", ni.getType(), "created for disequality normalization" );
							Node sk3 = NodeManager::currentNM()->mkSkolem( "z_dsplit_$$", ni.getType(), "created for disequality normalization" );
							Node lsk1 = getLength( sk1 );
							conc.push_back( lsk1.eqNode( li ) );
							Node lsk2 = getLength( sk2 );
							conc.push_back( lsk2.eqNode( lj ) );
							conc.push_back( NodeManager::currentNM()->mkNode( kind::OR,
												j.eqNode( mkConcat( sk1, sk3 ) ), i.eqNode( mkConcat( sk2, sk3 ) ) ) );
							
							sendLemma( mkExplain( antec, antec_new_lits ), NodeManager::currentNM()->mkNode( kind::AND, conc ), "Disequality Normalize" );
							return true;
						}else if( areEqual( li, lj ) ){
							if( areDisequal( i, j ) ){
								Trace("strings-solve") << "Case 1 : found equal length disequal sub strings " << i << " " << j << std::endl;
								//we are done
								return false;
							} else {
								//splitting on demand : try to make them disequal
								Node eq = i.eqNode( j );
								sendSplit( i, j, "Disequality : disequal terms" );
								eq = Rewriter::rewrite( eq );
								d_pending_req_phase[ eq ] = false;
								return true;
							}
						}else{
							//splitting on demand : try to make lengths equal
							Node eq = li.eqNode( lj );
							sendSplit( li, lj, "Disequality : equal length" );
							eq = Rewriter::rewrite( eq );
							d_pending_req_phase[ eq ] = true;
							return true;
						}
					}
				}
				index++;
			}
		}
		Assert( false );
	}
	return false;
}

void TheoryStrings::addNormalFormPair( Node n1, Node n2 ) {
  if( !isNormalFormPair( n1, n2 ) ){
		//Assert( !isNormalFormPair( n1, n2 ) );
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

void TheoryStrings::sendLemma( Node ant, Node conc, const char * c ) {
	if( conc.isNull() || conc==d_false ){
		d_out->conflict(ant);
		Trace("strings-conflict") << "Strings::Conflict : " << ant << std::endl;
		d_conflict = true;
	}else{
		Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, ant, conc );
		if( ant == d_true ) {
			lem = conc;
		}
		Trace("strings-lemma") << "Strings::Lemma " << c << " : " << lem << std::endl;
		d_lemma_cache.push_back( lem );
	}
}

void TheoryStrings::sendSplit( Node a, Node b, const char * c ) {
	Node eq = a.eqNode( b );
	eq = Rewriter::rewrite( eq );
	Node neq = NodeManager::currentNM()->mkNode( kind::NOT, eq );
	Node lemma_or = NodeManager::currentNM()->mkNode( kind::OR, eq, neq );
	Trace("strings-lemma") << "Strings::Lemma " << c << " SPLIT : " << lemma_or << std::endl;
	d_lemma_cache.push_back(lemma_or);
	d_pending_req_phase[eq] = true;
}

Node TheoryStrings::mkConcat( Node n1, Node n2 ) {
	std::vector< Node > c;
	c.push_back( n1 );
	c.push_back( n2 );
	return mkConcat( c );
}

Node TheoryStrings::mkConcat( std::vector< Node >& c ) {
    Node cc = c.size()>1 ? NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, c ) : ( c.size()==1 ? c[0] : d_emptyString );
	return Rewriter::rewrite( cc );
}

Node TheoryStrings::mkExplain( std::vector< Node >& a ) {
	std::vector< Node > an;
	return mkExplain( a, an );
}

Node TheoryStrings::mkExplain( std::vector< Node >& a, std::vector< Node >& an ) {
    std::vector< TNode > antec_exp;
    for( unsigned i=0; i<a.size(); i++ ){
		if( std::find( a.begin(), a.begin() + i, a[i] )==a.begin() + i ){
			bool exp = true;
			Trace("strings-solve-debug") << "Ask for explanation of " << a[i] << std::endl;
			//assert
			if(a[i].getKind() == kind::EQUAL) {
				//assert( hasTerm(a[i][0]) );
				//assert( hasTerm(a[i][1]) );
				Assert( areEqual(a[i][0], a[i][1]) );
				if( a[i][0]==a[i][1] ){
					exp = false;
				}
			} else if( a[i].getKind()==kind::NOT && a[i][0].getKind()==kind::EQUAL ){
				Assert( hasTerm(a[i][0][0]) );
				Assert( hasTerm(a[i][0][1]) );
				AlwaysAssert( d_equalityEngine.areDisequal(a[i][0][0], a[i][0][1], true) );
			}
			if( exp ){
				unsigned ps = antec_exp.size();
				explain(a[i], antec_exp);
				Trace("strings-solve-debug") << "Done, explanation was : " << std::endl;
				for( unsigned j=ps; j<antec_exp.size(); j++ ){
					Trace("strings-solve-debug") << "  " << antec_exp[j] << std::endl;
				}
				Trace("strings-solve-debug") << std::endl;
			}
		}
    }
    for( unsigned i=0; i<an.size(); i++ ){
		if( std::find( an.begin(), an.begin() + i, an[i] )==an.begin() + i ){
			Trace("strings-solve-debug") << "Add to explanation (new literal) " << an[i] << std::endl;
			antec_exp.push_back(an[i]);
		}
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

void TheoryStrings::getConcatVec( Node n, std::vector< Node >& c ) {
	if( n.getKind()==kind::STRING_CONCAT ){
		for( unsigned i=0; i<n.getNumChildren(); i++ ){
			if( !areEqual( n[i], d_emptyString ) ){
				c.push_back( n[i] );
			}
		}
	}else{
		c.push_back( n );
	}
}

bool TheoryStrings::checkLengths() {
  bool addedLemma = false;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ) {
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
			if( n.getKind() == kind::CONST_STRING || n.getKind() == kind::STRING_CONCAT ) { // || n.getKind() == kind::STRING_CONCAT ){
				if( d_length_inst.find(n)==d_length_inst.end() ) {
					d_length_inst[n] = true;
					Trace("strings-debug") << "get n: " << n << endl;
					Node sk = NodeManager::currentNM()->mkSkolem( "lsym_$$", n.getType(), "created for concat lemma" );
					d_length_intro_vars.push_back( sk );
					Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, sk, n );
					eq = Rewriter::rewrite(eq);
					Trace("strings-lemma") << "Strings::Lemma LENGTH term : " << eq << std::endl;
					d_out->lemma(eq);
					Node skl = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
					Node lsum;
					if( n.getKind() == kind::STRING_CONCAT ) {
						//add lemma
						std::vector<Node> node_vec;
						for( unsigned i=0; i<n.getNumChildren(); i++ ) {
							Node lni = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n[i] );
							node_vec.push_back(lni);
						}
						lsum = NodeManager::currentNM()->mkNode( kind::PLUS, node_vec );
					} else {
						//add lemma
						lsum = NodeManager::currentNM()->mkConst( ::CVC4::Rational( n.getConst<String>().size() ) );
					}
					Node ceq = NodeManager::currentNM()->mkNode( kind::EQUAL, skl, lsum );
					ceq = Rewriter::rewrite(ceq);
					Trace("strings-lemma") << "Strings::Lemma LENGTH : " << ceq << std::endl;
					d_out->lemma(ceq);
					addedLemma = true;
				}
			}
			++eqc_i;
		}
	}
	++eqcs_i;
  }
  return addedLemma;
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
			Trace("strings-eqc") << "Eqc( " << eqc << " ) : { ";
			while( !eqc2_i.isFinished() ) {
				if( (*eqc2_i)!=eqc ){
					Trace("strings-eqc") << (*eqc2_i) << " ";
				}
				++eqc2_i;
			}
			Trace("strings-eqc") << " } " << std::endl;
			EqcInfo * ei = getOrMakeEqcInfo( eqc, false );
			if( ei ){
				Trace("strings-eqc-debug") << "* Length term : " << ei->d_length_term.get() << std::endl;
				Trace("strings-eqc-debug") << "* Cardinality lemma k : " << ei->d_cardinality_lem_k.get() << std::endl;
				Trace("strings-eqc-debug") << "* Normalization length lemma : " << ei->d_normalized_length.get() << std::endl;
			}
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
	/*
	Trace("strings-nf") << "Current inductive equations : " << std::endl;
	for( NodeListMap::const_iterator it = d_ind_map1.begin(); it != d_ind_map1.end(); ++it ){
        Node x = (*it).first;
        NodeList* lst1 = (*it).second;
        NodeList* lst2 = (*d_ind_map2.find(x)).second;
        NodeList::const_iterator i1 = lst1->begin();
        NodeList::const_iterator i2 = lst2->begin();
        while( i1!=lst1->end() ){
            Node y = *i1;
            Node z = *i2;
			Trace("strings-nf") << "Inductive equation : " << x << " = ( " << y << " ++ " << z << " ) * " << y << std::endl;
            ++i1;
            ++i2;
        }
    }
	*/

  bool addedFact;
  do {
	Trace("strings-process") << "Check Normal Forms........next round" << std::endl;
    //calculate normal forms for each equivalence class, possibly adding splitting lemmas
    d_normal_forms.clear();
    d_normal_forms_exp.clear();
    std::map< Node, Node > nf_to_eqc;
    std::map< Node, Node > eqc_to_exp;
    d_lemma_cache.clear();
	d_pending_req_phase.clear();
	//get equivalence classes
	std::vector< Node > eqcs;
	getEquivalenceClasses( eqcs );
	for( unsigned i=0; i<eqcs.size(); i++ ){
		Node eqc = eqcs[i];
		Trace("strings-process") << "- Verify normal forms are the same for " << eqc << std::endl;
		std::vector< Node > visited;
		std::vector< Node > nf;
		std::vector< Node > nf_exp;
		normalizeEquivalenceClass(eqc, visited, nf, nf_exp);
		Trace("strings-debug") << "Finished normalizing eqc..." << std::endl;
		if( d_conflict ){
			doPendingFacts();
			doPendingLemmas();
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

	  Trace("strings-nf-debug") << "**** Normal forms are : " << std::endl;
	  for( std::map< Node, Node >::iterator it = nf_to_eqc.begin(); it != nf_to_eqc.end(); ++it ){
		Trace("strings-nf-debug") << "  normal_form(" << it->second << ") = " << it->first << std::endl;
	  }
	  Trace("strings-nf-debug") << std::endl;
      addedFact = !d_pending.empty();
      doPendingFacts();
  } while ( !d_conflict && d_lemma_cache.empty() && addedFact );

  //process disequalities between equivalence classes
  if( !d_conflict && d_lemma_cache.empty() ){
	  std::vector< Node > eqcs;
	  getEquivalenceClasses( eqcs );
	  std::vector< std::vector< Node > > cols;
	  std::vector< Node > lts;
	  seperateByLength( eqcs, cols, lts );
	  for( unsigned i=0; i<cols.size(); i++ ){
	    if( cols[i].size()>1 && d_lemma_cache.empty() ){
			Trace("strings-solve") << "- Verify disequalities are processed for ";
			printConcat( d_normal_forms[cols[i][0]], "strings-solve" );
			Trace("strings-solve")  << "..." << std::endl;
			//must ensure that normal forms are disequal
			for( unsigned j=1; j<cols[i].size(); j++ ){
				if( !d_equalityEngine.areDisequal( cols[i][0], cols[i][j], false ) ){
					sendSplit( cols[i][0], cols[i][j], "Disequality Normalization" );
					break;
				}else{
					Trace("strings-solve") << "  against ";
					printConcat( d_normal_forms[cols[i][j]], "strings-solve" );
					Trace("strings-solve")  << "..." << std::endl;
					if( normalizeDisequality( cols[i][0], cols[i][j] ) ){
						break;
					}
				}
			}
		}
	  }
  }

  //flush pending lemmas
  if( !d_lemma_cache.empty() ){
	doPendingLemmas();
	return true;
  }else{
	return false;
  }
}

bool TheoryStrings::checkLengthsEqc() {
	bool addedLemma = false;
	std::vector< Node > nodes;
	getEquivalenceClasses( nodes );
	for( unsigned i=0; i<nodes.size(); i++ ){
		if( d_normal_forms[nodes[i]].size()>1 ) {
			Trace("strings-process-debug") << "Process length constraints for " << nodes[i] << std::endl;
			//check if there is a length term for this equivalence class
			EqcInfo* ei = getOrMakeEqcInfo( nodes[i], false );
			Node lt = ei ? ei->d_length_term : Node::null();
			if( !lt.isNull() ) {
				Node llt = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt );
				//now, check if length normalization has occurred
				if( ei->d_normalized_length.get().isNull() ) {
					//if not, add the lemma
					std::vector< Node > ant;
					ant.insert( ant.end(), d_normal_forms_exp[nodes[i]].begin(), d_normal_forms_exp[nodes[i]].end() );
					ant.push_back( d_normal_forms_base[nodes[i]].eqNode( lt ) );
					Node lc = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, mkConcat( d_normal_forms[nodes[i]] ) );
					lc = Rewriter::rewrite( lc );
					Node eq = llt.eqNode( lc );
					ei->d_normalized_length.set( eq );
					sendLemma( mkExplain( ant ), eq, "Length Normalization" );
					addedLemma = true;
				}
			}
		}else{
			Trace("strings-process-debug") << "Do not process length constraints for " << nodes[i] << " " << d_normal_forms[nodes[i]].size() << std::endl;
		}
	}
	if( addedLemma ){
		doPendingLemmas();
	}
	return addedLemma;
}

bool TheoryStrings::checkCardinality() {
  int cardinality = options::stringCharCardinality();
  Trace("strings-solve-debug2") << "get cardinality: " << cardinality << endl;

  std::vector< Node > eqcs;
  getEquivalenceClasses( eqcs );

  std::vector< std::vector< Node > > cols;
  std::vector< Node > lts;
  seperateByLength( eqcs, cols, lts );

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
					sendSplit( *itr1, *itr2, "Cardinality" );
					doPendingLemmas();
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
				/*
				sendLemma( antc, cons, "Cardinality" );
				ei->d_cardinality_lem_k.set( int_k+1 );
				if( !d_lemma_cache.empty() ){
					doPendingLemmas();
					return true;
				}
				*/
                Node lemma = NodeManager::currentNM()->mkNode( kind::IMPLIES, antc, cons );
				lemma = Rewriter::rewrite( lemma );
				ei->d_cardinality_lem_k.set( int_k+1 );
				if( lemma!=d_true ){
					Trace("strings-lemma") << "Strings cardinality lemma : " << lemma << std::endl;
					d_out->lemma(lemma);
					return true;
				}
            }
        }
    }
  }
  return false;
}

void TheoryStrings::getEquivalenceClasses( std::vector< Node >& eqcs ) {
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
    while( !eqcs_i.isFinished() ) {
        Node eqc = (*eqcs_i);
        //if eqc.getType is string
        if (eqc.getType().isString()) {
			eqcs.push_back( eqc );
        }
        ++eqcs_i;
    }
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

void TheoryStrings::seperateByLength( std::vector< Node >& n, std::vector< std::vector< Node > >& cols,
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

void TheoryStrings::printConcat( std::vector< Node >& n, const char * c ) {
	for( unsigned i=0; i<n.size(); i++ ){
		if( i>0 ) Trace(c) << " ++ ";
		Trace(c) << n[i];
	}
}


//// Measurements
/*
void TheoryStrings::updateMpl( Node n, int b ) {
	if(d_mpl.find(n) == d_mpl.end()) {
		//d_curr_cardinality.get();
		d_mpl[n] = b;
	} else if(b < d_mpl[n]) {
		d_mpl[n] = b;
	}
}
*/

//// Regular Expressions
bool TheoryStrings::unrollStar( Node atom ) {
	Node x = atom[0];
	Node r = atom[1];
	int depth = d_reg_exp_unroll_depth.find( atom )==d_reg_exp_unroll_depth.end() ? 0 : d_reg_exp_unroll_depth[atom];
	if( depth <= d_regexp_unroll_depth ) {
		Trace("strings-regexp") << "Strings::Regexp: Unroll " << atom << " for " << ( depth + 1 ) << " times." << std::endl;
		d_reg_exp_unroll[atom] = true;
		//add lemma?
		Node xeqe = x.eqNode( d_emptyString );
		xeqe = Rewriter::rewrite( xeqe );
		d_pending_req_phase[xeqe] = true;
		Node sk_s= NodeManager::currentNM()->mkSkolem( "s_unroll_$$", x.getType(), "created for unrolling" );
		Node sk_xp= NodeManager::currentNM()->mkSkolem( "x_unroll_$$", x.getType(), "created for unrolling" );
		std::vector< Node >cc;

		// must also call preprocessing on unr1
		Node unr1 = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, sk_s, r[0] ) );
		if(unr1.getKind() == kind::EQUAL) {
			sk_s = unr1[0] == sk_s ? unr1[1] : unr1[2];
			Node unr0 = sk_s.eqNode( d_emptyString ).negate();
			cc.push_back(unr0);
		} else {
			std::vector< Node > urc;
			urc.push_back( unr1 );

			StringsPreprocess spp;
			spp.simplify( urc );
			for( unsigned i=1; i<urc.size(); i++ ){
				//add the others as lemmas
				sendLemma( d_true, urc[i], "RegExp Definition");
			}
			Node unr0 = sk_s.eqNode( d_emptyString ).negate();
			cc.push_back(unr0);	cc.push_back(urc[0]);
		}

		Node unr2 = x.eqNode( mkConcat( sk_s, sk_xp ) );
		Node unr3 = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, sk_xp, r );
		unr3 = Rewriter::rewrite( unr3 );
		d_reg_exp_unroll_depth[unr3] = depth + 1;
		if( d_reg_exp_ant.find( atom )!=d_reg_exp_ant.end() ){
			d_reg_exp_ant[unr3] = d_reg_exp_ant[atom];
		}

		//|x|>|xp|
		Node len_x_gt_len_xp = NodeManager::currentNM()->mkNode( kind::GT, 
								NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, x ),
								NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk_xp ) );

		cc.push_back(unr2); cc.push_back(unr3); cc.push_back(len_x_gt_len_xp);

		Node unr = NodeManager::currentNM()->mkNode( kind::AND, cc );
		Node lem = NodeManager::currentNM()->mkNode( kind::OR, xeqe, unr );
		Node ant = atom;
		if( d_reg_exp_ant.find( atom )!=d_reg_exp_ant.end() ) {
			ant = d_reg_exp_ant[atom];
		}
		sendLemma( ant, lem, "Unroll" );
		return true;
	}else{
		Trace("strings-regexp") << "Strings::regexp: Stop unrolling " << atom << " the max (" << depth << ") is reached." << std::endl;
		return false;
	}
}

bool TheoryStrings::checkMemberships() {
	bool is_unk = false;
	bool addedLemma = false;
	for( unsigned i=0; i<d_reg_exp_mem.size(); i++ ){
		//check regular expression membership
		Node assertion = d_reg_exp_mem[i];
		Trace("strings-regexp") << "We have regular expression assertion : " << assertion << std::endl;
		Node atom = assertion.getKind()==kind::NOT ? assertion[0] : assertion;
		bool polarity = assertion.getKind()!=kind::NOT;
		if( polarity ) {
			Assert( atom.getKind()==kind::STRING_IN_REGEXP );
			Node x = atom[0];
			Node r = atom[1];
			Assert( r.getKind()==kind::REGEXP_STAR );
			if( !areEqual( x, d_emptyString ) ) {
				/*if(d_opt_regexp_gcd) {
					if(d_membership_length.find(atom) == d_membership_length.end()) {
						addedLemma = addMembershipLength(atom);
						d_membership_length[atom] = true;
					} else {
						Trace("strings-regexp") << "Membership length is already added." << std::endl;
					}
				}*/
				bool flag = true;
				if( d_reg_exp_deriv.find(atom)==d_reg_exp_deriv.end() ) {
					if(splitRegExp( x, r, atom )) {
						addedLemma = true; flag = false;
						d_reg_exp_deriv[ atom ] = true;
					}
				} else {
					flag = false;
					Trace("strings-regexp-derivative") << "... is processed by deriv." << std::endl;
				}
				if( flag && d_reg_exp_unroll.find(atom)==d_reg_exp_unroll.end() ) {
					if( unrollStar( atom ) ) {
						addedLemma = true;
					} else {
						Trace("strings-regexp") << "RegExp is incomplete due to " << assertion << ", depth = " << d_regexp_unroll_depth << std::endl;
						is_unk = true;
					}
				} else {
					Trace("strings-regexp") << "...is already unrolled or splitted." << std::endl;
				}
			} else {
				Trace("strings-regexp") << "...is satisfied." << std::endl;
			}
		} else {
			//TODO: negative membership
			//Node r = Rewriter::rewrite( atom[1] );
			//r = d_regexp_opr.complement( r );
			//Trace("strings-regexp-test") << "Compl( " << d_regexp_opr.mkString( atom[1] ) << " ) is " << d_regexp_opr.mkString( r ) << std::endl;
			//Trace("strings-regexp-test") << "Delta( " << d_regexp_opr.mkString( atom[1] ) << " ) is " << d_regexp_opr.delta( atom[1] ) << std::endl;
			//Trace("strings-regexp-test") << "Delta( " << d_regexp_opr.mkString( r ) << " ) is " << d_regexp_opr.delta( r ) << std::endl;
			//Trace("strings-regexp-test") << "Deriv( " << d_regexp_opr.mkString( r ) << ", c='b' ) is " << d_regexp_opr.mkString( d_regexp_opr.derivativeSingle( r, ::CVC4::String("b") ) ) << std::endl;
			//Trace("strings-regexp-test") << "FHC( " << d_regexp_opr.mkString( r ) <<" ) is " << std::endl;
			//d_regexp_opr.firstChar( r );
			//r = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, atom[0], r );
			/*
			std::vector< Node > vec_r;
			vec_r.push_back( r );

			StringsPreprocess spp;
			spp.simplify( vec_r );
			for( unsigned i=1; i<vec_r.size(); i++ ){
				if(vec_r[i].getKind() == kind::STRING_IN_REGEXP) {
					d_reg_exp_mem.push_back( vec_r[i] );
				} else if(vec_r[i].getKind() == kind::EQUAL) {
					d_equalityEngine.assertEquality(vec_r[i], true, vec_r[i]);
				} else {
					Assert(false);
				}
			}
			*/
			Trace("strings-regexp") << "RegEx is incomplete due to " << assertion << "." << std::endl;
			is_unk = true;
		}
	}
	if( addedLemma ){
		doPendingLemmas();
		return true;
	}else{
		if( is_unk ){
			//if(!d_opt_fmf) {
			//	d_opt_fmf = true;
				//d_regexp_unroll_depth += 2;
			//	Node t = getNextDecisionRequest();
			//	return !t.isNull();
			//} else {
				Trace("strings-regexp") << "Strings::regexp: possibly incomplete." << std::endl;
				//d_regexp_incomplete = true;
				d_out->setIncomplete();
			//}
		}
		return false;
	}
}

CVC4::String TheoryStrings::getHeadConst( Node x ) {
	if( x.isConst() ) {
		return x.getConst< String >();
	} else if( x.getKind() == kind::STRING_CONCAT ) {
		if( x[0].isConst() ) {
			return x[0].getConst< String >();
		} else {
			return d_emptyString.getConst< String >();
		}
	} else {
		return d_emptyString.getConst< String >();
	}
}

bool TheoryStrings::addMembershipLength(Node atom) {
	Node x = atom[0];
	Node r = atom[1];

	/*std::vector< int > co;
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
	}*/
	return false;
}

bool TheoryStrings::splitRegExp( Node x, Node r, Node ant ) {
	// TODO cstr in vre
	Assert(x != d_emptyString);
	Trace("strings-regexp-split") << "TheoryStrings::splitRegExp: x=" << x << ", r= " << r << std::endl;
	CVC4::String s = getHeadConst( x );
	if( !s.isEmptyString() && d_regexp_opr.checkConstRegExp( r ) ) {
		Node conc = Node::null();
		Node dc = r;
		bool flag = true;
		for(unsigned i=0; i<s.size(); ++i) {
			CVC4::String c = s.substr(i, 1);
			dc = d_regexp_opr.derivativeSingle(dc, c);
			if(dc.isNull()) {
				// CONFLICT
				flag = false;
				break;
			}
		}
		// send lemma
		if(flag) {
			if(x.isConst()) {
				/*
				left = d_emptyString;
				if(d_regexp_opr.delta(dc) == 1) {
					//TODO yes possible?
				} else if(d_regexp_opr.delta(dc) == 0) {
					//TODO possible?
				} else {
					// TODO conflict possible?
				}*/
				Assert(false, "Impossible: TheoryStrings::splitRegExp: const string in const regular expression.");
				return false;
			} else {
				Assert( x.getKind() == kind::STRING_CONCAT );
				std::vector< Node > vec_nodes;
				for(unsigned int i=1; i<x.getNumChildren(); ++i ) {
					vec_nodes.push_back( x[i] );
				}
				Node left = vec_nodes.size() == 1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, vec_nodes );
				left = Rewriter::rewrite( left );
				conc = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, left, dc );

				std::vector< Node > sdc;
				sdc.push_back( conc );

				StringsPreprocess spp;
				spp.simplify( sdc );
				for( unsigned i=1; i<sdc.size(); i++ ){
					//add the others as lemmas
					sendLemma( d_true, sdc[i], "RegExp Definition");
				}
				
				conc = sdc[0];
			}
		}
		sendLemma(ant, conc, "RegExp Const Split");
		return true;
	} else {
		return false;
	}
}

//// Finite Model Finding

Node TheoryStrings::getNextDecisionRequest() {
	if(d_opt_fmf && !d_conflict) {
		//Trace("strings-fmf-debug") << "Strings::FMF: Assertion Level = " << d_valuation.getAssertionLevel() << std::endl;
		//initialize the term we will minimize
		if( d_in_var_lsum.isNull() && !d_in_vars.empty() ){
			Trace("strings-fmf-debug") << "Input variables: ";
			std::vector< Node > ll;
			for(std::vector< Node >::iterator itr = d_in_vars.begin();
				itr != d_in_vars.end(); ++itr) {
				Trace("strings-fmf-debug") << " " << (*itr) ;
				ll.push_back( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, *itr ) );
			}
			Trace("strings-fmf-debug") << std::endl;
			d_in_var_lsum = ll.size()==1 ? ll[0] : NodeManager::currentNM()->mkNode( kind::PLUS, ll );
			d_in_var_lsum = Rewriter::rewrite( d_in_var_lsum );
		}
		if( !d_in_var_lsum.isNull() ){
			//Trace("strings-fmf") << "Get next decision request." << std::endl;
			//check if we need to decide on something
			int decideCard = d_curr_cardinality.get();
			if( d_cardinality_lits.find( decideCard )!=d_cardinality_lits.end() ){
				bool value;
				if( d_valuation.hasSatValue( d_cardinality_lits[ d_curr_cardinality.get() ], value ) ) {
					if( !value ){
						d_curr_cardinality.set( d_curr_cardinality.get() + 1 );
						decideCard = d_curr_cardinality.get();
						Trace("strings-fmf-debug") << "Has false SAT value, increment and decide." << std::endl;
					}else{
						decideCard = -1;
						Trace("strings-fmf-debug") << "Has true SAT value, do not decide." << std::endl;
					}
				}else{
					Trace("strings-fmf-debug") << "No SAT value, decide." << std::endl;
				}
			}
			if( decideCard!=-1 ){
				if( d_cardinality_lits.find( decideCard )==d_cardinality_lits.end() ){
					Node lit = NodeManager::currentNM()->mkNode( kind::LEQ, d_in_var_lsum, NodeManager::currentNM()->mkConst( Rational( decideCard ) ) );
					lit = Rewriter::rewrite( lit );
					d_cardinality_lits[decideCard] = lit;
					Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit, lit.negate() );
					Trace("strings-fmf") << "Strings FMF: Add split lemma " << lem << ", decideCard = " << decideCard << std::endl;
					d_out->lemma( lem );
					d_out->requirePhase( lit, true );
				}
				Trace("strings-fmf") << "Strings FMF: Decide positive on " << d_cardinality_lits[ decideCard ] << std::endl;
				return d_cardinality_lits[ decideCard ];
			}
		}
	}

	return Node::null();
}

void TheoryStrings::assertNode( Node lit ) {
}

Node TheoryStrings::mkSplitEq( const char * c, const char * info, Node lhs, Node rhs, bool lgtZero ) {
	Node sk = NodeManager::currentNM()->mkSkolem( c, lhs.getType(), info );
	Node eq = lhs.eqNode( mkConcat( rhs, sk ) );
	eq = Rewriter::rewrite( eq );
	if( lgtZero ) {
		d_var_lgtz[sk] = true;
		Node sk_gt_zero = NodeManager::currentNM()->mkNode( kind::EQUAL, sk, d_emptyString).negate();
		Trace("strings-lemma") << "Strings::Lemma sk GT zero: " << sk_gt_zero << std::endl;
		d_lemma_cache.push_back( sk_gt_zero );
	}
	//store it in proper map
	if( options::stringFMF() ){
		d_var_split_graph_lhs[sk] = lhs;
		d_var_split_graph_rhs[sk] = rhs;
		//d_var_split_eq[sk] = eq;
		
		//int mpl = getMaxPossibleLength( sk );
		Trace("strings-progress") << "Strings::Progress: Because of " << eq << std::endl;
		Trace("strings-progress") << "Strings::Progress: \t" << lhs << "(up:" << getMaxPossibleLength(lhs) << ") is removed" << std::endl;
		Trace("strings-progress") << "Strings::Progress: \t" << sk << "(up:" << getMaxPossibleLength(sk) << ") is added" << std::endl;
	}
	return eq;
}

int TheoryStrings::getMaxPossibleLength( Node x ) {
	if( d_var_split_graph_lhs.find( x )==d_var_split_graph_lhs.end() ){
		if( x.getKind()==kind::CONST_STRING ){
			return x.getConst<String>().size();
		}else{
			return d_curr_cardinality.get();
		}
	}else{
		return getMaxPossibleLength( d_var_split_graph_lhs[x] ) - 1;
	}
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
