/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of strings
 **
 ** Theory of strings.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__THEORY_STRINGS_H
#define __CVC4__THEORY__STRINGS__THEORY_STRINGS_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/strings/regexp_operation.h"

#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Decision procedure for strings.
 *
 */

class TheoryStrings : public Theory {
	typedef context::CDChunkList<Node> NodeList;
	typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeListMap;
	typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
	typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;

public:
	TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe);
	~TheoryStrings();

	void setMasterEqualityEngine(eq::EqualityEngine* eq);

	std::string identify() const { return std::string("TheoryStrings"); }

public:
	void propagate(Effort e);
	bool propagate(TNode literal);
	void explain( TNode literal, std::vector<TNode>& assumptions );
	Node explain( TNode literal );


	// NotifyClass for equality engine
	class NotifyClass : public eq::EqualityEngineNotify {
		TheoryStrings& d_str;
	public:
		NotifyClass(TheoryStrings& t_str): d_str(t_str) {}
		bool eqNotifyTriggerEquality(TNode equality, bool value) {
		  Debug("strings") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
		  if (value) {
			return d_str.propagate(equality);
		  } else {
			// We use only literal triggers so taking not is safe
			return d_str.propagate(equality.notNode());
		  }
		}
		bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
		  Debug("strings") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
		  if (value) {
			return d_str.propagate(predicate);
		  } else {
		   return d_str.propagate(predicate.notNode());
		  }
		}
		bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
		  Debug("strings") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
		  if (value) {
			return d_str.propagate(t1.eqNode(t2));
		  } else {
			return d_str.propagate(t1.eqNode(t2).notNode());
		  }
		}
		void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
		  Debug("strings") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
		  d_str.conflict(t1, t2);
		}
		void eqNotifyNewClass(TNode t) {
		  Debug("strings") << "NotifyClass::eqNotifyNewClass(" << t << std::endl;
		  d_str.eqNotifyNewClass(t);
		}
		void eqNotifyPreMerge(TNode t1, TNode t2) {
		  Debug("strings") << "NotifyClass::eqNotifyPreMerge(" << t1 << ", " << t2 << std::endl;
		  d_str.eqNotifyPreMerge(t1, t2);
		}
		void eqNotifyPostMerge(TNode t1, TNode t2) {
		  Debug("strings") << "NotifyClass::eqNotifyPostMerge(" << t1 << ", " << t2 << std::endl;
		  d_str.eqNotifyPostMerge(t1, t2);
		}
		void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
		  Debug("strings") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << std::endl;
		  d_str.eqNotifyDisequal(t1, t2, reason);
		}
	};/* class TheoryStrings::NotifyClass */

private:
	// Constants
    Node d_emptyString;
    Node d_true;
    Node d_false;
    Node d_zero;
	// Options
	bool d_opt_fmf;
	bool d_opt_regexp_gcd;
	// Helper functions
	Node getRepresentative( Node t );
	bool hasTerm( Node a );
	bool areEqual( Node a, Node b );
	bool areDisequal( Node a, Node b );
	Node getLengthTerm( Node t );
	Node getLength( Node t );

private:
    /** The notify class */
    NotifyClass d_notify;
    /** Equaltity engine */
    eq::EqualityEngine d_equalityEngine;
    /** Are we in conflict */
    context::CDO<bool> d_conflict;
	std::vector< Node > d_length_intro_vars;
	//list of pairs of nodes to merge
	std::map< Node, Node > d_pending_exp;
	std::vector< Node > d_pending;
	std::vector< Node > d_lemma_cache;
	std::map< Node, bool > d_pending_req_phase;
	/** inferences */
	NodeList d_infer;
	NodeList d_infer_exp;
	/** normal forms */
	std::map< Node, Node > d_normal_forms_base;
	std::map< Node, std::vector< Node > > d_normal_forms;
	std::map< Node, std::vector< Node > > d_normal_forms_exp;
	//map of pairs of terms that have the same normal form
	NodeListMap d_nf_pairs;
	void addNormalFormPair( Node n1, Node n2 );
	bool isNormalFormPair( Node n1, Node n2 );
	bool isNormalFormPair2( Node n1, Node n2 );
	// loop ant
	std::map< Node, bool > d_loop_antec;

	/////////////////////////////////////////////////////////////////////////////
	// MODEL GENERATION
	/////////////////////////////////////////////////////////////////////////////
public:
	void collectModelInfo(TheoryModel* m, bool fullModel);

	/////////////////////////////////////////////////////////////////////////////
	// NOTIFICATIONS
	/////////////////////////////////////////////////////////////////////////////
public:
	void presolve();
	void shutdown() { }

	/////////////////////////////////////////////////////////////////////////////
	// MAIN SOLVER
	/////////////////////////////////////////////////////////////////////////////
private:
	void addSharedTerm(TNode n);
	EqualityStatus getEqualityStatus(TNode a, TNode b);

private:
	class EqcInfo {
	public:
		EqcInfo( context::Context* c );
		~EqcInfo(){}
		//constant in this eqc
		context::CDO< Node > d_const_term;
		context::CDO< Node > d_length_term;
		context::CDO< unsigned > d_cardinality_lem_k;
		// 1 = added length lemma
		context::CDO< Node > d_normalized_length;
	};
	/** map from representatives to information necessary for equivalence classes */
	std::map< Node, EqcInfo* > d_eqc_info;
	EqcInfo * getOrMakeEqcInfo( Node eqc, bool doMake = true );
	//maintain which concat terms have the length lemma instantiatied
	std::map< Node, bool > d_length_inst;
private:
    bool getNormalForms(Node &eqc, std::vector< Node > & visited, std::vector< Node > & nf,
						std::vector< std::vector< Node > > &normal_forms,
						std::vector< std::vector< Node > > &normal_forms_exp,
						std::vector< Node > &normal_form_src);
	bool detectLoop(std::vector< std::vector< Node > > &normal_forms,
					int i, int j, int index_i, int index_j, 
					int &loop_in_i, int &loop_in_j);
	bool processLoop(std::vector< Node > &antec,
					 std::vector< std::vector< Node > > &normal_forms,
					 std::vector< Node > &normal_form_src,
					 int i, int j, int loop_n_index, int other_n_index,
					 int loop_index, int index, int other_index);
	bool processNEqc(std::vector< std::vector< Node > > &normal_forms,
					 std::vector< std::vector< Node > > &normal_forms_exp,
					 std::vector< Node > &normal_form_src);
    bool normalizeEquivalenceClass( Node n, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp );
    bool normalizeDisequality( Node n1, Node n2 );
	bool unrollStar( Node atom );

	bool checkLengths();
    bool checkNormalForms();
	bool checkLengthsEqc();
    bool checkCardinality();
    bool checkInductiveEquations();
	bool checkMemberships();

public:
	void preRegisterTerm(TNode n);
	void check(Effort e);

	/** Conflict when merging two constants */
	void conflict(TNode a, TNode b);
	/** called when a new equivalance class is created */
	void eqNotifyNewClass(TNode t);
	/** called when two equivalance classes will merge */
	void eqNotifyPreMerge(TNode t1, TNode t2);
	/** called when two equivalance classes have merged */
	void eqNotifyPostMerge(TNode t1, TNode t2);
	/** called when two equivalence classes are made disequal */
	void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
protected:
	/** compute care graph */
	void computeCareGraph();

	//do pending merges
	void doPendingFacts();
	void doPendingLemmas();

	void sendLemma( Node ant, Node conc, const char * c );
	void sendSplit( Node a, Node b, const char * c );
	/** mkConcat **/
	Node mkConcat( Node n1, Node n2 );
	Node mkConcat( std::vector< Node >& c );
	/** mkExplain **/
	Node mkExplain( std::vector< Node >& a );
	Node mkExplain( std::vector< Node >& a, std::vector< Node >& an );
	/** get concat vector */
	void getConcatVec( Node n, std::vector< Node >& c );

	//get equivalence classes
	void getEquivalenceClasses( std::vector< Node >& eqcs );
	//get final normal form
	void getFinalNormalForm( Node n, std::vector< Node >& nf, std::vector< Node >& exp );

	//seperate into collections with equal length
	void seperateByLength( std::vector< Node >& n, std::vector< std::vector< Node > >& col, std::vector< Node >& lts );
	void printConcat( std::vector< Node >& n, const char * c );

	// Measurement
private:
	//NodeIntMap d_var_lmin;
	//NodeIntMap d_var_lmax;
	std::map< Node, Node > d_var_split_graph_lhs;
	std::map< Node, Node > d_var_split_graph_rhs;
	std::map< Node, bool > d_var_lgtz;
	Node mkSplitEq( const char * c, const char * info, Node lhs, Node rhs, bool lgtZero );
	int getMaxPossibleLength( Node x );

	// Regular Expression
private:
	// regular expression memberships
	NodeList d_reg_exp_mem;
	// antecedant for why reg exp membership must be true
	std::map< Node, Node > d_reg_exp_ant;
	std::map< Node, bool > d_reg_exp_unroll;
	std::map< Node, int > d_reg_exp_unroll_depth;
	bool d_regexp_incomplete;
	int d_regexp_unroll_depth;
	int d_regexp_max_depth;
	// membership length
	std::map< Node, bool > d_membership_length;
	// regular expression derivative
	std::map< Node, bool > d_reg_exp_deriv;
	// regular expression operations
	RegExpOpr d_regexp_opr;

	CVC4::String getHeadConst( Node x );
	bool splitRegExp( Node x, Node r, Node ant );
	bool addMembershipLength(Node atom);


	// Finite Model Finding
private:
	std::vector< Node > d_in_vars;
	Node d_in_var_lsum;
	std::map< int, Node > d_cardinality_lits;
	context::CDO< int > d_curr_cardinality;
public:
	//for finite model finding
    Node getNextDecisionRequest();
	void assertNode( Node lit );

};/* class TheoryStrings */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
