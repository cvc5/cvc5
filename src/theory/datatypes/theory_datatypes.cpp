/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of datatypes
 **
 ** Implementation of the theory of datatypes.
 **/


#include "theory/datatypes/theory_datatypes.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "util/datatype.h"
#include "util/cvc4_assert.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes_type_rules.h"
#include "theory/theory_model.h"
#include "smt/options.h"
#include "smt/boolean_terms.h"
#include "theory/quantifiers/options.h"
#include "theory/datatypes/options.h"
#include "theory/type_enumerator.h"

#include <map>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;


TheoryDatatypes::TheoryDatatypes(Context* c, UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_DATATYPES, c, u, out, valuation, logicInfo),
  //d_cycle_check(c),
  d_hasSeenCycle(c, false),
  d_infer(c),
  d_infer_exp(c),
  d_notify( *this ),
  d_equalityEngine(d_notify, c, "theory::datatypes::TheoryDatatypes"),
  d_labels( c ),
  d_selector_apps( c ),
  d_conflict( c, false ),
  d_collectTermsCache( c ){

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_SELECTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_TESTER);
}

TheoryDatatypes::~TheoryDatatypes() {
}

void TheoryDatatypes::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

TheoryDatatypes::EqcInfo* TheoryDatatypes::getOrMakeEqcInfo( Node n, bool doMake ){
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
  if( !hasEqcInfo( n ) ){
    if( doMake ){
      //add to labels
      NodeList* lbl = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                             ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_labels.insertDataFromContextMemory( n, lbl );
      EqcInfo* ei;
      if( eqc_i!=d_eqc_info.end() ){
        ei = eqc_i->second;
      }else{
        ei = new EqcInfo( getSatContext() );
        d_eqc_info[n] = ei;
      }
      if( n.getKind()==APPLY_CONSTRUCTOR ){
        ei->d_constructor = n;
      }
      //add to selectors
      NodeList* sel = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                               ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_selector_apps.insertDataFromContextMemory( n, sel );
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*eqc_i).second;
  }
}

void TheoryDatatypes::check(Effort e) {
  Trace("datatypes-debug") << "Check effort " << e << std::endl;
  while(!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;
    Trace("datatypes-assert") << "Assert " << fact << std::endl;

    TNode atom CVC4_UNUSED = fact.getKind() == kind::NOT ? fact[0] : fact;

    // extra debug check to make sure that the rewriter did its job correctly
    Assert( atom.getKind() != kind::EQUAL ||
            ( atom[0].getKind() != kind::TUPLE && atom[1].getKind() != kind::TUPLE &&
              atom[0].getKind() != kind::RECORD && atom[1].getKind() != kind::RECORD &&
              atom[0].getKind() != kind::TUPLE_UPDATE && atom[1].getKind() != kind::TUPLE_UPDATE &&
              atom[0].getKind() != kind::RECORD_UPDATE && atom[1].getKind() != kind::RECORD_UPDATE &&
              atom[0].getKind() != kind::TUPLE_SELECT && atom[1].getKind() != kind::TUPLE_SELECT &&
              atom[0].getKind() != kind::RECORD_SELECT && atom[1].getKind() != kind::RECORD_SELECT ),
            "tuple/record escaped into datatypes decision procedure; should have been rewritten away" );

    //assert the fact
    assertFact( fact, fact );
    flushPendingFacts();
  }

  if( e == EFFORT_FULL ) {
    //check for cycles
    checkCycles();
    if( d_conflict ){
      return;
    }
    //check for splits
    Debug("datatypes-split") << "Check for splits " << e << endl;
    bool addedFact = false;
    do {
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
      while( !eqcs_i.isFinished() ){
        Node n = (*eqcs_i);
        if( DatatypesRewriter::isTermDatatype( n ) ){
          Trace("datatypes-debug") << "Process equivalence class " << n << std::endl;
          EqcInfo* eqc = getOrMakeEqcInfo( n, true );
          //if there are more than 1 possible constructors for eqc
          if( eqc->d_constructor.get().isNull() && !hasLabel( eqc, n ) ) {
            Trace("datatypes-debug") << "No constructor..." << std::endl;
            const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
            //if only one constructor, then this term must be this constructor
            if( dt.getNumConstructors()==1 ){
              Node t = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[0].getTester() ), n );
              d_pending.push_back( t );
              d_pending_exp[ t ] = NodeManager::currentNM()->mkConst( true );
              Trace("datatypes-infer") << "DtInfer : " << t << ", trivial" << std::endl;
              d_infer.push_back( t );
            }else{
              std::vector< bool > pcons;
              getPossibleCons( eqc, n, pcons );
              //std::cout << "pcons " << n << " = ";
              //for( int i=0; i<(int)pcons.size(); i++ ){ //std::cout << pcons[i] << " "; }
              //std::cout << std::endl;
              //check if we do not need to resolve the constructor type for this equivalence class.
              // this is if there are no selectors for this equivalence class, its possible values are infinite,
              //  and we are not producing a model, then do not split.
              int consIndex = -1;
              bool needSplit = true;
              for( unsigned int j=0; j<pcons.size(); j++ ) {
                if( pcons[j] ) {
                  if( consIndex==-1 ){
                    consIndex = j;
                  }
                  if( !dt[ j ].isFinite() && !eqc->d_selectors ) {
                    needSplit = false;
                  }
                }
              }
              /*
              if( !needSplit && mustSpecifyAssignment() ){
                //for the sake of termination, we must choose the constructor of a ground term
                //NEED GUARENTEE: groundTerm should not contain any subterms of the same type
                // TODO: this is probably not good enough, actually need fair enumeration strategy
                Node groundTerm = n.getType().mkGroundTerm();
                int index = Datatype::indexOf( groundTerm.getOperator().toExpr() );
                if( pcons[index] ){
                  consIndex = index;
                }
                needSplit = true;
              }
              */
              if( needSplit && consIndex!=-1 ) {
                Node test = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[consIndex].getTester() ), n );
                Trace("dt-split") << "*************Split for possible constructor " << dt[consIndex] << " for " << n <<  endl;
                test = Rewriter::rewrite( test );
                NodeBuilder<> nb(kind::OR);
                nb << test << test.notNode();
                Node lemma = nb;
                d_out->lemma( lemma );
                d_out->requirePhase( test, true );
                return;
              }else{
                Trace("dt-split-debug") << "Do not split constructor for " << n << std::endl;
              }
            }
          }else{
            Trace("datatypes-debug") << "Has constructor " << eqc->d_constructor.get() << std::endl;
          }
        }
        ++eqcs_i;
      }
      Trace("datatypes-debug") << "Flush pending facts..."  << std::endl;
      addedFact = !d_pending.empty() || !d_pending_merge.empty();
      flushPendingFacts();
      /*
      if( !d_conflict ){
        if( options::dtRewriteErrorSel() ){
          bool innerAddedFact = false;
          do {
            collapseSelectors();
            innerAddedFact = !d_pending.empty() || !d_pending_merge.empty();
            flushPendingFacts();
          }while( !d_conflict && innerAddedFact );
        }
      }
      */
    }while( !d_conflict && addedFact );
    Trace("datatypes-debug") << "Finished. " << d_conflict << std::endl;
    if( !d_conflict ){
      Trace("dt-model-test") << std::endl;
      printModelDebug("dt-model-test");
    }
  }

  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ) {
    Notice() << "TheoryDatatypes::check(): done" << endl;
  }
}

void TheoryDatatypes::flushPendingFacts(){
  doPendingMerges();
  if( !d_pending.empty() ){
    int i = 0;
    while( !d_conflict && i<(int)d_pending.size() ){
      Node fact = d_pending[i];
      Node exp = d_pending_exp[ fact ];
      //check to see if we have to communicate it to the rest of the system
      if( mustCommunicateFact( fact, exp ) ){
        Trace("dt-lemma-debug") << "Assert fact " << fact << " " << exp << std::endl;
        Node lem = fact;
        if( exp.isNull() || exp==NodeManager::currentNM()->mkConst( true ) ){
          lem = fact;
        }else{
          Trace("dt-lemma-debug") << "Get explanation..." << std::endl;
          Node ee_exp = explain( exp );
          Trace("dt-lemma-debug") << "Explanation : " << ee_exp << std::endl;
          lem = NodeManager::currentNM()->mkNode( IMPLIES, ee_exp, fact );
          lem = Rewriter::rewrite( lem );
        }
        Trace("dt-lemma") << "Datatypes lemma : " << lem << std::endl;
        d_out->lemma( lem );
      }else{
        assertFact( fact, exp );
      }
      i++;
    }
    d_pending.clear();
    d_pending_exp.clear();
  }
}

void TheoryDatatypes::doPendingMerges(){
  //do all pending merges
  int i=0;
  while( i<(int)d_pending_merge.size() ){
    Assert( d_pending_merge[i].getKind()==EQUAL || d_pending_merge[i].getKind()==IFF );
    merge( d_pending_merge[i][0], d_pending_merge[i][1] );
    i++;
  }
  d_pending_merge.clear();
}

void TheoryDatatypes::assertFact( Node fact, Node exp ){
  Assert( d_pending_merge.empty() );
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.assertEquality( atom, polarity, exp );
  }else{
    d_equalityEngine.assertPredicate( atom, polarity, exp );
  }
  doPendingMerges();
  //add to tester if applicable
  if( atom.getKind()==kind::APPLY_TESTER ){
    Node rep = getRepresentative( atom[0] );
    EqcInfo* eqc = getOrMakeEqcInfo( rep, true );
    addTester( fact, eqc, rep );
  }
  doPendingMerges();
}

void TheoryDatatypes::preRegisterTerm(TNode n) {
  Debug("datatypes-prereg") << "TheoryDatatypes::preRegisterTerm() " << n << endl;
  collectTerms( n );
  switch (n.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(n);
    break;
  case kind::APPLY_TESTER:
    // Get triggered for both equal and dis-equal
    d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
    // Maybe it's a predicate
    if (n.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(n);
    } else {
      // Function applications/predicates
      d_equalityEngine.addTerm(n);
    }
    break;
  }
  flushPendingFacts();
}

void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
}

Node TheoryDatatypes::ppRewrite(TNode in) {
  Debug("tuprec") << "TheoryDatatypes::ppRewrite(" << in << ")" << endl;

  if(in.getKind() == kind::TUPLE_SELECT) {
    TypeNode t = in[0].getType();
    if(t.hasAttribute(expr::DatatypeTupleAttr())) {
      t = t.getAttribute(expr::DatatypeTupleAttr());
    }
    TypeNode dtt = NodeManager::currentNM()->getDatatypeForTupleRecord(t);
    const Datatype& dt = DatatypeType(dtt.toType()).getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR, Node::fromExpr(dt[0][in.getOperator().getConst<TupleSelect>().getIndex()].getSelector()), in[0]);
  } else if(in.getKind() == kind::RECORD_SELECT) {
    TypeNode t = in[0].getType();
    if(t.hasAttribute(expr::DatatypeRecordAttr())) {
      t = t.getAttribute(expr::DatatypeRecordAttr());
    }
    TypeNode dtt = NodeManager::currentNM()->getDatatypeForTupleRecord(t);
    const Datatype& dt = DatatypeType(dtt.toType()).getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR, Node::fromExpr(dt[0][in.getOperator().getConst<RecordSelect>().getField()].getSelector()), in[0]);
  }

  TypeNode t = in.getType();

  // we only care about tuples and records here
  if(in.getKind() != kind::TUPLE && in.getKind() != kind::TUPLE_UPDATE &&
     in.getKind() != kind::RECORD && in.getKind() != kind::RECORD_UPDATE) {
    if((t.isTuple() || t.isRecord()) && in.hasAttribute(smt::BooleanTermAttr())) {
      Debug("tuprec") << "should map " << in << " of type " << t << " back to " << in.getAttribute(smt::BooleanTermAttr()).getType() << endl;
      Debug("tuprec") << "so " << NodeManager::currentNM()->getDatatypeForTupleRecord(t).getDatatype() << " goes to " << NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getDatatype() << endl;
      if(t.isTuple()) {
        Debug("tuprec") << "current datatype-tuple-attr is " << NodeManager::currentNM()->getDatatypeForTupleRecord(t).getAttribute(expr::DatatypeTupleAttr()) << endl;
        Debug("tuprec") << "setting to " << NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeTupleAttr()) << endl;
        NodeManager::currentNM()->getDatatypeForTupleRecord(t).setAttribute(expr::DatatypeTupleAttr(), NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeTupleAttr()));
      } else {
        Debug("tuprec") << "current datatype-record-attr is " << NodeManager::currentNM()->getDatatypeForTupleRecord(t).getAttribute(expr::DatatypeRecordAttr()) << endl;
        Debug("tuprec") << "setting to " << NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeRecordAttr()) << endl;
        NodeManager::currentNM()->getDatatypeForTupleRecord(t).setAttribute(expr::DatatypeRecordAttr(), NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeRecordAttr()));
      }
    }
    // nothing to do
    return in;
  }

  if(t.hasAttribute(expr::DatatypeTupleAttr())) {
    t = t.getAttribute(expr::DatatypeTupleAttr());
  } else if(t.hasAttribute(expr::DatatypeRecordAttr())) {
    t = t.getAttribute(expr::DatatypeRecordAttr());
  }

  // if the type doesn't have an associated datatype, then make one for it
  TypeNode dtt = (t.isTuple() || t.isRecord()) ? NodeManager::currentNM()->getDatatypeForTupleRecord(t) : t;

  const Datatype& dt = DatatypeType(dtt.toType()).getDatatype();

  // now rewrite the expression
  Node n;
  if(in.getKind() == kind::TUPLE || in.getKind() == kind::RECORD) {
    NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
    b << Node::fromExpr(dt[0].getConstructor());
    b.append(in.begin(), in.end());
    n = b;
  } else if(in.getKind() == kind::TUPLE_UPDATE || in.getKind() == kind::RECORD_UPDATE) {
    NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
    b << Node::fromExpr(dt[0].getConstructor());
    size_t size, updateIndex;
    if(in.getKind() == kind::TUPLE_UPDATE) {
      size = t.getNumChildren();
      updateIndex = in.getOperator().getConst<TupleUpdate>().getIndex();
    } else { // kind::RECORD_UPDATE
      const Record& record = t.getConst<Record>();
      size = record.getNumFields();
      updateIndex = record.getIndex(in.getOperator().getConst<RecordUpdate>().getField());
    }
    Debug("tuprec") << "expr is " << in << std::endl;
    Debug("tuprec") << "updateIndex is " << updateIndex << std::endl;
    Debug("tuprec") << "t is " << t << std::endl;
    Debug("tuprec") << "t has arity " << size << std::endl;
    for(size_t i = 0; i < size; ++i) {
      if(i == updateIndex) {
        b << in[1];
        Debug("tuprec") << "arg " << i << " gets updated to " << in[1] << std::endl;
      } else {
        b << NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR, Node::fromExpr(dt[0][i].getSelector()), in[0]);
        Debug("tuprec") << "arg " << i << " copies " << b[b.getNumChildren() - 1] << std::endl;
      }
    }
    Debug("tuprec") << "builder says " << b << std::endl;
    n = b;
  }

  Assert(!n.isNull());

  Debug("tuprec") << "REWROTE " << in << " to " << n << std::endl;

  return n;
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  if( t.getType().isBoolean() ){
    //d_equalityEngine.addTriggerPredicate(t, THEORY_DATATYPES);
  }else{
    d_equalityEngine.addTriggerTerm(t, THEORY_DATATYPES);
  }
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm() finished" << std::endl;
}

/** propagate */
void TheoryDatatypes::propagate(Effort effort){

}

/** propagate */
bool TheoryDatatypes::propagate(TNode literal){
  Debug("dt::propagate") << "TheoryDatatypes::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("dt::propagate") << "TheoryDatatypes::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  Trace("dt-prop") << "dtPropagate " << literal << std::endl;
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

/** explain */
void TheoryDatatypes::explain(TNode literal, std::vector<TNode>& assumptions){
  Debug("datatypes-explain") << "Explain " << literal << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> tassumptions;
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
}

Node TheoryDatatypes::explain( TNode literal ){
  std::vector< TNode > assumptions;
  explain( literal, assumptions );
  return mkAnd( assumptions );
}

/** Conflict when merging two constants */
void TheoryDatatypes::conflict(TNode a, TNode b){
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain( a.iffNode(b) );
  } else {
    d_conflictNode = explain( a.eqNode(b) );
  }
  Trace("dt-conflict") << "CONFLICT: Eq engine conflict : " << d_conflictNode << std::endl;
  d_out->conflict( d_conflictNode );
  d_conflict = true;
}

/** called when a new equivalance class is created */
void TheoryDatatypes::eqNotifyNewClass(TNode t){
  if( t.getKind()==APPLY_CONSTRUCTOR ){
    getOrMakeEqcInfo( t, true );
  }
}

/** called when two equivalance classes will merge */
void TheoryDatatypes::eqNotifyPreMerge(TNode t1, TNode t2){

}

/** called when two equivalance classes have merged */
void TheoryDatatypes::eqNotifyPostMerge(TNode t1, TNode t2){
  if( DatatypesRewriter::isTermDatatype( t1 ) ){
    d_pending_merge.push_back( t1.eqNode( t2 ) );
  }
}

void TheoryDatatypes::merge( Node t1, Node t2 ){
  if( !d_conflict ){
    Node trep1 = t1;
    Node trep2 = t2;
    Debug("datatypes-debug") << "Merge " << t1 << " " << t2 << std::endl;
    EqcInfo* eqc2 = getOrMakeEqcInfo( t2 );
    if( eqc2 ){
      bool checkInst = false;
      if( !eqc2->d_constructor.get().isNull() ){
        trep2 = eqc2->d_constructor.get();
      }
      EqcInfo* eqc1 = getOrMakeEqcInfo( t1 );
      if( eqc1 ){
        if( !eqc1->d_constructor.get().isNull() ){
          trep1 = eqc1->d_constructor.get();
        }
        //check for clash
        Node cons1 = eqc1->d_constructor;
        Node cons2 = eqc2->d_constructor;
        //if both have constructor, then either clash or unification
        if( !cons1.isNull() && !cons2.isNull() ){
          Debug("datatypes-debug") << "Constructors : " << cons1 << " " << cons2 << std::endl;
          if( cons1.getOperator()!=cons2.getOperator() ){
            //check for clash
            d_conflictNode = explain( cons1.eqNode( cons2 ) );
            Trace("dt-conflict") << "CONFLICT: Clash conflict : " << d_conflictNode << std::endl;
            d_out->conflict( d_conflictNode );
            d_conflict = true;
            return;
          }else{
            //do unification
            Node unifEq = cons1.eqNode( cons2 );
            for( int i=0; i<(int)cons1.getNumChildren(); i++ ) {
              if( cons1[i]!=cons2[i] ){
                Node eq = cons1[i].getType().isBoolean() ? cons1[i].iffNode( cons2[i] ) : cons1[i].eqNode( cons2[i] );
                d_pending.push_back( eq );
                d_pending_exp[ eq ] = unifEq;
                Trace("datatypes-infer") << "DtInfer : " << eq << " by " << unifEq << std::endl;
                d_infer.push_back( eq );
                d_infer_exp.push_back( unifEq );
              }
            }
          }
        }
        if( !eqc1->d_inst && eqc2->d_inst ){
          eqc1->d_inst = true;
        }
        if( cons1.isNull() && !cons2.isNull() ){
          Debug("datatypes-debug") << "Must check if it is okay to set the constructor." << std::endl;
          checkInst = true;
          addConstructor( eqc2->d_constructor.get(), eqc1, t1 );
          if( d_conflict ){
            return;
          }
        }
      }else{
        Debug("datatypes-debug") << "No eqc info for " << t1 << ", must create" << std::endl;
        //just copy the equivalence class information
        eqc1 = getOrMakeEqcInfo( t1, true );
        eqc1->d_inst.set( eqc2->d_inst );
        eqc1->d_constructor.set( eqc2->d_constructor );
        eqc1->d_selectors.set( eqc2->d_selectors );
      }


      //merge labels
      NodeListMap::iterator lbl_i = d_labels.find( t2 );
      if( lbl_i != d_labels.end() ){
        Debug("datatypes-debug") << "Merge labels from " << eqc2 << " " << t2 << std::endl;
        NodeList* lbl = (*lbl_i).second;
        for( NodeList::const_iterator j = lbl->begin(); j != lbl->end(); ++j ){
          addTester( *j, eqc1, t1 );
          if( d_conflict ){
            Debug("datatypes-debug") << "Conflict!" << std::endl;
            return;
          }
        }
      }
      //merge selectors
      if( !eqc1->d_selectors && eqc2->d_selectors ){
        eqc1->d_selectors = true;
        checkInst = true;
      }
      NodeListMap::iterator sel_i = d_selector_apps.find( t2 );
      if( sel_i != d_selector_apps.end() ){
        Debug("datatypes-debug") << "Merge selectors from " << eqc2 << " " << t2 << std::endl;
        NodeList* sel = (*sel_i).second;
        for( NodeList::const_iterator j = sel->begin(); j != sel->end(); ++j ){
          addSelector( *j, eqc1, t1, eqc2->d_constructor.get().isNull() );
        }
      }
      if( checkInst ){
        instantiate( eqc1, t1 );
        if( d_conflict ){
          return;
        }
      }
    }
    //add this to the transitive closure module
    Node oldRep = trep2;
    Node newRep = trep1;
    if( trep1.getKind()!=APPLY_CONSTRUCTOR && trep2.getKind()==APPLY_CONSTRUCTOR ){
      oldRep = trep1;
      newRep = trep2;
    }
    /*
    bool result = d_cycle_check.addEdgeNode( oldRep, newRep );
    //d_hasSeenCycle.set( d_hasSeenCycle.get() || result );
    Debug("datatypes-cycles") << "DtCyc: Equal " << oldRep << " -> " << newRep << " " << result << " " << d_hasSeenCycle.get() << endl;
    if( result ){
      checkCycles();
      if( d_conflict ){
        Debug("datatypes-cycles-find") << "Cycle found." << std::endl;
        return;
      }else{
        Debug("datatypes-cycles-find") << "WARNING : no cycle found." << std::endl;
        d_cycle_check.debugPrint();
      }
    }
    */
  }
}

/** called when two equivalence classes are made disequal */
void TheoryDatatypes::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){

}

TheoryDatatypes::EqcInfo::EqcInfo( context::Context* c ) :
d_inst( c, false ), d_constructor( c, Node::null() ), d_selectors( c, false ){

}

bool TheoryDatatypes::hasLabel( EqcInfo* eqc, Node n ){
  return !eqc->d_constructor.get().isNull() || !getLabel( n ).isNull();
}

Node TheoryDatatypes::getLabel( Node n ) {
  NodeListMap::iterator lbl_i = d_labels.find( n );
  if( lbl_i != d_labels.end() ){
    NodeList* lbl = (*lbl_i).second;
    if( !(*lbl).empty() && (*lbl)[ (*lbl).size() - 1 ].getKind()==kind::APPLY_TESTER ){
      return (*lbl)[ (*lbl).size() - 1 ];
    }
  }
  return Node::null();
}

int TheoryDatatypes::getLabelIndex( EqcInfo* eqc, Node n ){
  if( !eqc->d_constructor.get().isNull() ){
    return Datatype::indexOf( eqc->d_constructor.get().getOperator().toExpr() );
  }else{
    return Datatype::indexOf( getLabel( n ).getOperator().toExpr() );
  }
}

void TheoryDatatypes::getPossibleCons( EqcInfo* eqc, Node n, std::vector< bool >& pcons ){
  const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
  pcons.resize( dt.getNumConstructors(), !hasLabel( eqc, n ) );
  if( hasLabel( eqc, n ) ){
    pcons[ getLabelIndex( eqc, n ) ] = true;
  }else{
    NodeListMap::iterator lbl_i = d_labels.find( n );
    if( lbl_i != d_labels.end() ){
      NodeList* lbl = (*lbl_i).second;
      for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
        Assert( (*i).getKind()==NOT );
        pcons[ Datatype::indexOf( (*i)[0].getOperator().toExpr() ) ] = false;
      }
    }
  }
}

void TheoryDatatypes::addTester( Node t, EqcInfo* eqc, Node n ){
  Debug("datatypes-debug") << "Add tester : " << t << " to eqc(" << n << ")" << std::endl;
  Debug("datatypes-labels") << "Add tester " << t << " " << n << " " << eqc << std::endl;
  bool tpolarity = t.getKind()!=NOT;
  Node tt = ( t.getKind() == NOT ) ? t[0] : t;
  int ttindex = Datatype::indexOf( tt.getOperator().toExpr() );
  Node j, jt;
  bool makeConflict = false;
  if( hasLabel( eqc, n ) ){
    //if we already know the constructor type, check whether it is in conflict or redundant
    int jtindex = getLabelIndex( eqc, n );
    if( (jtindex==ttindex)!=tpolarity ){
      if( !eqc->d_constructor.get().isNull() ){
        //conflict because equivalence class contains a constructor
        std::vector< TNode > assumptions;
        explain( t, assumptions );
        explain( eqc->d_constructor.get().eqNode( tt[0] ), assumptions );
        d_conflictNode = mkAnd( assumptions );
        Trace("dt-conflict") << "CONFLICT: Tester eq conflict : " << d_conflictNode << std::endl;
        d_out->conflict( d_conflictNode );
        d_conflict = true;
        return;
      }else{
        makeConflict = true;
        //conflict because the existing label is contradictory
        j = getLabel( n );
        jt = j;
      }
    }else{
      return;
    }
  }else{
    //otherwise, scan list of labels
    NodeListMap::iterator lbl_i = d_labels.find( n );
    Assert( lbl_i != d_labels.end() );
    NodeList* lbl = (*lbl_i).second;
    for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
      Assert( (*i).getKind()==NOT );
      j = *i;
      jt = j[0];
      int jtindex = Datatype::indexOf( jt.getOperator().toExpr() );
      if( jtindex==ttindex ){
        if( tpolarity ){  //we are in conflict
          makeConflict = true;
          break;
        }else{            //it is redundant
          return;
        }
      }
    }
    if( !makeConflict ){
      Debug("datatypes-labels") << "Add to labels " << t << std::endl;
      lbl->push_back( t );
      const Datatype& dt = ((DatatypeType)(tt[0].getType()).toType()).getDatatype();
      Debug("datatypes-labels") << "Labels at " << lbl->size() << " / " << dt.getNumConstructors() << std::endl;
      if( tpolarity ){
        instantiate( eqc, n );
      }else{
        //check if we have reached the maximum number of testers
        // in this case, add the positive tester
        if( lbl->size()==dt.getNumConstructors()-1 ){
          std::vector< bool > pcons;
          getPossibleCons( eqc, n, pcons );
          int testerIndex = -1;
          for( int i=0; i<(int)pcons.size(); i++ ) {
            if( pcons[i] ){
              testerIndex = i;
              break;
            }
          }
          Assert( testerIndex!=-1 );
          //we must explain why each term in the set of testers for this equivalence class is equal
          std::vector< Node > eq_terms;
          NodeBuilder<> nb(kind::AND);
          for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
            nb << (*i);
            if( std::find( eq_terms.begin(), eq_terms.end(), (*i)[0][0] )==eq_terms.end() ){
              eq_terms.push_back( (*i)[0][0] );
              if( (*i)[0][0]!=tt[0] ){
                nb << (*i)[0][0].eqNode( tt[0] );
              }
            }
          }
          Node t_concl = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[unsigned(testerIndex)].getTester() ), tt[0] );
          Node t_concl_exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
          d_pending.push_back( t_concl );
          d_pending_exp[ t_concl ] = t_concl_exp;
          Trace("datatypes-infer") << "DtInfer : " << t_concl << " by " << t_concl_exp << std::endl;
          d_infer.push_back( t_concl );
          d_infer_exp.push_back( t_concl_exp );
          return;
        }
      }
    }
  }
  if( makeConflict ){
    d_conflict = true;
    Debug("datatypes-labels") << "Explain " << j << " " << t << std::endl;
    std::vector< TNode > assumptions;
    explain( j, assumptions );
    explain( t, assumptions );
    explain( jt[0].eqNode( tt[0] ), assumptions );
    d_conflictNode = mkAnd( assumptions );
    Trace("dt-conflict") << "CONFLICT: Tester conflict : " << d_conflictNode << std::endl;
    d_out->conflict( d_conflictNode );
  }
}

void TheoryDatatypes::addSelector( Node s, EqcInfo* eqc, Node n, bool assertFacts ) {
  Debug("datatypes-debug") << "Add selector : " << s << " to eqc(" << n << ")" << std::endl;
  //check to see if it is redundant
  NodeListMap::iterator sel_i = d_selector_apps.find( n );
  Assert( sel_i != d_selector_apps.end() );
  if( sel_i != d_selector_apps.end() ){
    NodeList* sel = (*sel_i).second;
    for( NodeList::const_iterator j = sel->begin(); j != sel->end(); ++j ){
      Node ss = *j;
      if( s.getOperator()==ss.getOperator() ){
        return;
      }
    }
    //add it to the vector
    sel->push_back( s );
    eqc->d_selectors = true;
  }
  if( assertFacts && !eqc->d_constructor.get().isNull() ){
    //conclude the collapsed merge
    collapseSelector( s, eqc->d_constructor.get() );
  }
}

void TheoryDatatypes::addConstructor( Node c, EqcInfo* eqc, Node n ){
  Debug("datatypes-debug") << "Add constructor : " << c << " to eqc(" << n << ")" << std::endl;
  Assert( eqc->d_constructor.get().isNull() );
  //check labels
  NodeListMap::iterator lbl_i = d_labels.find( n );
  if( lbl_i != d_labels.end() ){
    size_t constructorIndex = Datatype::indexOf(c.getOperator().toExpr());
    NodeList* lbl = (*lbl_i).second;
    for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
      if( (*i).getKind()==NOT ){
        if( Datatype::indexOf( (*i)[0].getOperator().toExpr() )==constructorIndex ){
          Node n = *i;
          std::vector< TNode > assumptions;
          explain( *i, assumptions );
          explain( c.eqNode( (*i)[0][0] ), assumptions );
          d_conflictNode = mkAnd( assumptions );
          Trace("dt-conflict") << "CONFLICT: Tester merge eq conflict : " << d_conflictNode << std::endl;
          d_out->conflict( d_conflictNode );
          d_conflict = true;
          return;
        }
      }
    }
  }
  //check selectors
  NodeListMap::iterator sel_i = d_selector_apps.find( n );
  if( sel_i != d_selector_apps.end() ){
    NodeList* sel = (*sel_i).second;
    for( NodeList::const_iterator j = sel->begin(); j != sel->end(); ++j ){
      //collapse the selector
      collapseSelector( *j, c );
    }
  }
  eqc->d_constructor.set( c );
}

void TheoryDatatypes::collapseSelector( Node s, Node c ) {
  Node r = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR, s.getOperator(), c );
  Node rr = Rewriter::rewrite( r );
  //if( r!=rr ){
    //Node eq_exp = NodeManager::currentNM()->mkConst(true);
    //Node eq = r.getType().isBoolean() ? r.iffNode( rr ) : r.eqNode( rr );
  if( s!=rr ){
    Node eq_exp = c.eqNode( s[0] );
    Node eq = rr.getType().isBoolean() ? s.iffNode( rr ) : s.eqNode( rr );


    d_pending.push_back( eq );
    d_pending_exp[ eq ] = eq_exp;
    Trace("datatypes-infer") << "DtInfer : " << eq << " by " << eq_exp << " (collapse selector)" << std::endl;
    d_infer.push_back( eq );
    d_infer_exp.push_back( eq_exp );
  }
}

EqualityStatus TheoryDatatypes::getEqualityStatus(TNode a, TNode b){
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

void TheoryDatatypes::computeCareGraph(){
  Theory::computeCareGraph();
}

void TheoryDatatypes::collectModelInfo( TheoryModel* m, bool fullModel ){
  Trace("dt-cmi") << "Datatypes : Collect model info " << d_equalityEngine.consistent() << std::endl;
  Trace("dt-model") << std::endl;
  printModelDebug( "dt-model" );
  Trace("dt-model") << std::endl;
  m->assertEqualityEngine( &d_equalityEngine );
/*
  std::vector< TypeEnumerator > vec;
  std::map< TypeNode, int > tes;
  */
  //get all constructors
  eq::EqClassesIterator eqccs_i = eq::EqClassesIterator( &d_equalityEngine );
  std::vector< Node > cons;
  while( !eqccs_i.isFinished() ){
    Node eqc = (*eqccs_i);
    //for all equivalence classes that are datatypes
    if( DatatypesRewriter::isTermDatatype( eqc ) ){
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      if( !ei->d_constructor.get().isNull() ){
        cons.push_back( ei->d_constructor.get() );
      }
    }
    ++eqccs_i;
  }

  //must choose proper representatives
  std::vector< Node > nodes;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    //for all equivalence classes that are datatypes
    if( DatatypesRewriter::isTermDatatype( eqc ) ){
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      if( !ei->d_constructor.get().isNull() ){
        //specify that we should use the constructor as the representative
        //m->assertRepresentative( ei->d_constructor.get() );
      }else{
        nodes.push_back( eqc );
      }
    }
    ++eqcs_i;
  }
  unsigned index = 0;
  while( index<nodes.size() ){
    Node eqc = nodes[index];
    Node neqc;
    if( !d_equalityEngine.hasTerm( eqc ) ){
      Trace("dt-cmi") << "NOTICE : Datatypes: need to assign constructor for " << eqc << std::endl;
      Trace("dt-cmi") << "   Type : " << eqc.getType() << std::endl;
      //can assign arbitrary term
      TypeEnumerator te(eqc.getType());
      bool success;
      do{
        success = true;
        Assert( !te.isFinished() );
        neqc = *te;
        Trace("dt-cmi-debug") << "Try " << neqc << " ... " << std::endl;
        ++te;
        for( unsigned i=0; i<cons.size(); i++ ){
          //check if it is modulo equality the same
          if( cons[i].getOperator()==neqc.getOperator() ){
            bool diff = false;
            for( unsigned j=0; j<cons[i].getNumChildren(); j++ ){
              if( !m->areEqual( cons[i][j], neqc[j] ) ){
                diff = true;
                break;
              }
            }
            if( !diff ){
              Trace("dt-cmi-debug") << "...Already equivalent modulo equality to " << cons[i] << std::endl;
              success = false;
              break;
            }
          }
        }
      }while( !success );
    }else{
      Trace("dt-cmi") << "NOTICE : Datatypes: no constructor in equivalence class " << eqc << std::endl;
      Trace("dt-cmi") << "   Type : " << eqc.getType() << std::endl;
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      std::vector< bool > pcons;
      getPossibleCons( ei, eqc, pcons );
      Trace("dt-cmi") << "Possible constructors : ";
      for( unsigned i=0; i<pcons.size(); i++ ){
        Trace("dt-cmi") << pcons[i] << " ";
      }
      Trace("dt-cmi") << std::endl;
      /*
      if( tes.find( eqc.getType() )==tes.end() ){
        tes[eqc.getType()]=vec.size();
        vec.push_back( TypeEnumerator( eqc.getType() ) );
      }
      bool success;
      Node n;
      do {
        success = true;
        Assert( !vec[tes[eqc.getType()]].isFinished() );
        n = *vec[tes[eqc.getType()]];
        ++vec[tes[eqc.getType()]];
        Trace("dt-cmi-debug") << "Try " << n << "..." << std::endl;
        //check if it is consistent with labels
        size_t constructorIndex = Datatype::indexOf(n.getOperator().toExpr());
        if( constructorIndex<pcons.size() && pcons[constructorIndex] ){
          for( unsigned i=0; i<cons.size(); i++ ){
            //check if it is modulo equality the same
            if( cons[i].getOperator()==n.getOperator() ){
              bool diff = false;
              for( unsigned j=0; j<cons[i].getNumChildren(); j++ ){
                if( !m->areEqual( cons[i][j], n[j] ) ){
                  diff = true;
                  break;
                }
              }
              if( !diff ){
                Trace("dt-cmi-debug") << "...Already equivalent modulo equality to " << cons[i] << std::endl;
                success = false;
                break;
              }
            }
          }
        }else{
          Trace("dt-cmi-debug") << "...Not consistent with labels" << std::endl;
          success = false;
        }
      }while( !success );
      */
      const Datatype& dt = ((DatatypeType)(eqc.getType()).toType()).getDatatype();
      for( unsigned r=0; r<2; r++ ){
        if( neqc.isNull() ){
          for( unsigned i=0; i<pcons.size(); i++ ){
            if( pcons[i] && (r==1)==dt[ i ].isFinite() ){
              neqc = getInstantiateCons( eqc, dt, i, false, false );
              for( unsigned j=0; j<neqc.getNumChildren(); j++ ){
                if( !d_equalityEngine.hasTerm( neqc[j] ) && DatatypesRewriter::isTermDatatype( neqc[j] ) ){
                  nodes.push_back( neqc[j] );
                }
              }
              break;
            }
          }
        }
      }
    }
    Assert( !neqc.isNull() );
    Trace("dt-cmi") << "Assign : " << neqc << std::endl;
    m->assertEquality( eqc, neqc, true );
    //m->assertRepresentative( neqc );
    cons.push_back( neqc );
    ++index;
  }

}


void TheoryDatatypes::collectTerms( Node n ) {
  if( d_collectTermsCache.find( n )==d_collectTermsCache.end() ){
    d_collectTermsCache[n] = true;
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      collectTerms( n[i] );
    }
    if( n.getKind() == APPLY_CONSTRUCTOR ){
      /*
      //we must take into account subterm relation when checking for cycles
      for( int i=0; i<(int)n.getNumChildren(); i++ ) {
        bool result = d_cycle_check.addEdgeNode( n, n[i] );
        Debug("datatypes-cycles") << "DtCyc: Subterm " << n << " -> " << n[i] << " " << result << endl;
        if( result && !d_hasSeenCycle.get() ){
          Debug("datatypes-cycles") << "FOUND CYCLE" << std::endl;
        }
        d_hasSeenCycle.set( d_hasSeenCycle.get() || result );
        //Node r = getRepresentative( n[i] );
        //EqcInfo* eqc = getOrMakeEqcInfo( r, true );
        //eqc->d_selectors = true;
      }
      */
    }else if( n.getKind() == APPLY_SELECTOR ){
      //we must also record which selectors exist
      Debug("datatypes") << "  Found selector " << n << endl;
      if (n.getType().isBoolean()) {
        d_equalityEngine.addTriggerPredicate( n );
      }else{
        d_equalityEngine.addTerm( n );
      }
      Node rep = getRepresentative( n[0] );
      //record it in the selectors
      EqcInfo* eqc = getOrMakeEqcInfo( rep, true );
      //add it to the eqc info
      addSelector( n, eqc, rep );
    }
  }
}

void TheoryDatatypes::processNewTerm( Node n ){
  Trace("dt-terms") << "Created term : " << n << std::endl;
  //see if it is rewritten to be something different
  Node rn = Rewriter::rewrite( n );
  if( rn!=n && !areEqual( rn, n ) ){
    Node eq = n.getType().isBoolean() ? rn.iffNode( n ) : rn.eqNode( n );
    d_pending.push_back( eq );
    d_pending_exp[ eq ] = NodeManager::currentNM()->mkConst( true );
    Trace("datatypes-infer") << "DtInfer : " << eq << ", trivial" << std::endl;
    d_infer.push_back( eq );
  }
}

Node TheoryDatatypes::getInstantiateCons( Node n, const Datatype& dt, int index, bool mkVar, bool isActive ){
  //if( !d_inst_map[n][index].isNull() ){
  //  return d_inst_map[n][index];
  //}else{
    //add constructor to equivalence class
    Type tspec;
    if( dt.isParametric() ){
      tspec = dt[index].getSpecializedConstructorType(n.getType().toType());
    }
    std::vector< Node > children;
    children.push_back( Node::fromExpr( dt[index].getConstructor() ) );
    for( int i=0; i<(int)dt[index].getNumArgs(); i++ ){
      Node nc = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[index][i].getSelector() ), n );
      if( mkVar ){
        TypeNode tn = nc.getType();
        if( dt.isParametric() ){
          tn = TypeNode::fromType( tspec )[i];
        }
        nc = NodeManager::currentNM()->mkSkolem( "m_$$", tn, "created during model gen" );
      }
      children.push_back( nc );
      if( isActive ){
        processNewTerm( nc );
      }
    }
    Node n_ic = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
    if( isActive ){
      collectTerms( n_ic );
    }
    //add type ascription for ambiguous constructor types
    if(!n_ic.getType().isComparableTo(n.getType())) {
      Assert( dt.isParametric() );
      Debug("datatypes-parametric") << "DtInstantiate: ambiguous type for " << n_ic << ", ascribe to " << n.getType() << std::endl;
      Debug("datatypes-parametric") << "Constructor is " << dt[index] << std::endl;
      Type tspec = dt[index].getSpecializedConstructorType(n.getType().toType());
      Debug("datatypes-parametric") << "Type specification is " << tspec << std::endl;
      children[0] = NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                                     NodeManager::currentNM()->mkConst(AscriptionType(tspec)), children[0] );
      n_ic = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
      Assert( n_ic.getType()==n.getType() );
    }
    n_ic = Rewriter::rewrite( n_ic );
    Debug("dt-enum") << "Made instantiate cons " << n_ic << std::endl;
    //d_inst_map[n][index] = n_ic;
    return n_ic;
  //}
}

void TheoryDatatypes::instantiate( EqcInfo* eqc, Node n ){
  //add constructor to equivalence class if not done so already
  if( hasLabel( eqc, n ) && !eqc->d_inst ){
    Node exp;
    Node tt;
    if( !eqc->d_constructor.get().isNull() ){
      exp = NodeManager::currentNM()->mkConst( true );
      tt = eqc->d_constructor;
    }else{
      exp = getLabel( n );
      tt = exp[0];
    }
    int index = getLabelIndex( eqc, n );
    const Datatype& dt = ((DatatypeType)(tt.getType()).toType()).getDatatype();
    //must be finite or have a selector
    //if( eqc->d_selectors || dt[ index ].isFinite() ){ // || mustSpecifyAssignment()
    //instantiate this equivalence class
    eqc->d_inst = true;
    Node tt_cons = getInstantiateCons( tt, dt, index );
    Node eq;
    if( tt!=tt_cons ){
      eq = tt.eqNode( tt_cons );
      Debug("datatypes-inst") << "DtInstantiate : " << eqc << " " << eq << std::endl;
      d_pending.push_back( eq );
      d_pending_exp[ eq ] = exp;
      Trace("datatypes-infer") << "DtInfer : " << eq << " by " << exp << std::endl;
      //eqc->d_inst.set( eq );
      d_infer.push_back( eq );
      d_infer_exp.push_back( exp );
    }
    //}
    //else{
    //  Debug("datatypes-inst") << "Do not instantiate" << std::endl;
    //}
  }
}

void TheoryDatatypes::checkCycles() {
  Debug("datatypes-cycle-check") << "Check cycles" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    if( DatatypesRewriter::isTermDatatype( eqc ) ) {
      map< Node, bool > visited;
      std::vector< TNode > expl;
      Node cn = searchForCycle( eqc, eqc, visited, expl );
      //if we discovered a different cycle while searching this one
      if( !cn.isNull() && cn!=eqc ){
        visited.clear();
        expl.clear();
        Node prev = cn;
        cn = searchForCycle( cn, cn, visited, expl );
        Assert( prev==cn );
      }

      if( !cn.isNull() ) {
        Assert( expl.size()>0 );
        d_conflictNode = mkAnd( expl );
        Trace("dt-conflict") << "CONFLICT: Cycle conflict : " << d_conflictNode << std::endl;
        d_out->conflict( d_conflictNode );
        d_conflict = true;
        return;
      }
    }
    ++eqcs_i;
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
Node TheoryDatatypes::searchForCycle( Node n, Node on,
                                      map< Node, bool >& visited,
                                      std::vector< TNode >& explanation, bool firstTime ) {
  Debug("datatypes-cycle-check") << "Search for cycle " << n << " " << on << endl;
  Node ncons;
  Node nn;
  if( !firstTime ){
    nn = getRepresentative( n );
    if( nn==on ){
      Node lit = NodeManager::currentNM()->mkNode( EQUAL, n, nn );
      explain( lit, explanation );
      return on;
    }
  }else{
    nn = n;
  }
  if( visited.find( nn ) == visited.end() ) {
    visited[nn] = true;
    EqcInfo* eqc = getOrMakeEqcInfo( nn, false );
    if( eqc ){
      Node ncons = eqc->d_constructor.get();
      if( !ncons.isNull() ) {
        for( int i=0; i<(int)ncons.getNumChildren(); i++ ) {
          Node cn = searchForCycle( ncons[i], on, visited, explanation, false );
          if( cn==on ) {
            //if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n, ncons[i] ) ){
            //  Debug("datatypes-cycles") << "Cycle subterm: " << n << " is not -> " << ncons[i] << "!!!!" << std::endl;
            //}
            //add explanation for why the constructor is connected
            if( n != ncons ) {
              Node lit = NodeManager::currentNM()->mkNode( EQUAL, n, ncons );
              explain( lit, explanation );
            }
            return on;
          }else if( !cn.isNull() ){
            return cn;
          }
        }
      }
    }
    visited.erase( nn );
    return Node::null();
  }else{
    return nn;
  }
}

bool TheoryDatatypes::mustSpecifyAssignment(){
  //FIXME: the condition finiteModelFind is an over-approximation in this function
  //   we still may not want to specify assignments for datatypes that are truly infinite
  //   the fix for this is to correctly compute the cardinality for datatypes containing uninterpered sorts in fmf (i.e. by assuming they are finite)
  return options::finiteModelFind() || options::produceModels() || options::dtForceAssignment();
  //return options::produceModels();
  //return false;
}

bool TheoryDatatypes::mustCommunicateFact( Node n, Node exp ){
  //the datatypes decision procedure makes 3 "internal" inferences apart from the equality engine :
  //  (1) Unification : C( t1...tn ) = C( s1...sn ) => ti = si
  //  (2) Label : ~is_C1( t ) ... ~is_C{i-1}( t ) ~is_C{i+1}( t ) ... ~is_Cn( t ) => is_Ci( t )
  //  (3) Instantiate : is_C( t ) => t = C( sel_1( t ) ... sel_n( t ) )
  //We may need to communicate (3) outwards if the conclusions involve other theories
  Trace("dt-lemma-debug") << "Compute for " << exp << " => " << n << std::endl;
  bool addLemma = false;
  if( ( n.getKind()==EQUAL || n.getKind()==IFF) && n[1].getKind()==APPLY_CONSTRUCTOR && exp.getKind()!=EQUAL  ){
#if 1
    const Datatype& dt = ((DatatypeType)(n[1].getType()).toType()).getDatatype();
    addLemma = dt.involvesExternalType();
#else
    for( int j=0; j<(int)n[1].getNumChildren(); j++ ){
      if( !DatatypesRewriter::isTermDatatype( n[1][j] ) ){
        addLemma = true;
        break;
      }
    }
#endif
    if( addLemma ){
      //check if we have already added this lemma
      if( std::find( d_inst_lemmas[ n[0] ].begin(), d_inst_lemmas[ n[0] ].end(), n[1] )==d_inst_lemmas[ n[0] ].end() ){
        d_inst_lemmas[ n[0] ].push_back( n[1] );
        Trace("dt-lemma-debug") << "Communicate " << n << std::endl;
        return true;
      }else{
        Trace("dt-lemma-debug") << "Already communicated " << n << std::endl;
        return false;
      }
    }
  }
  //else if( exp.getKind()==APPLY_TESTER ){
    //if( n.getKind()==EQUAL && !DatatypesRewriter::isTermDatatype( n[0] ) ){
    //  return true;
    //}
  //}
  Trace("dt-lemma-debug") << "Do not need to communicate " << n << std::endl;
  return false;
}

bool TheoryDatatypes::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryDatatypes::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryDatatypes::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

Node TheoryDatatypes::getRepresentative( Node a ){
  if( hasTerm( a ) ){
    return d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}


void TheoryDatatypes::printModelDebug( const char* c ){
  if(! (Trace.isOn(c))) {
    return;
  }

  Trace( c ) << "Datatypes model : " << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    if( !eqc.getType().isBoolean() ){
      if( DatatypesRewriter::isTermDatatype( eqc ) ){
        Trace( c ) << "DATATYPE : ";
      }
      Trace( c ) << eqc << " : " << eqc.getType() << " : " << std::endl;
      Trace( c ) << "   { ";
      //add terms to model
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ){
        Trace( c ) << (*eqc_i) << " ";
        ++eqc_i;
      }
      Trace( c ) << "}" << std::endl;
      if( DatatypesRewriter::isTermDatatype( eqc ) ){
        EqcInfo* ei = getOrMakeEqcInfo( eqc );
        if( ei ){
          Trace( c ) << "   Instantiated : " << ei->d_inst.get() << std::endl;
          Trace( c ) << "   Constructor : ";
          if( !ei->d_constructor.get().isNull() ){
            Trace( c )<< ei->d_constructor.get();
          }
          Trace( c ) << std::endl << "   Labels : ";
          if( hasLabel( ei, eqc ) ){
            Trace( c ) << getLabel( eqc );
          }else{
            NodeListMap::iterator lbl_i = d_labels.find( eqc );
            if( lbl_i != d_labels.end() ){
              NodeList* lbl = (*lbl_i).second;
              for( NodeList::const_iterator j = lbl->begin(); j != lbl->end(); j++ ){
                Trace( c ) << *j << " ";
              }
            }
          }
          Trace( c ) << std::endl;
          Trace( c ) << "   Selectors : " << ( ei->d_selectors ? "yes, " : "no " );
          NodeListMap::iterator sel_i = d_selector_apps.find( eqc );
          if( sel_i != d_selector_apps.end() ){
            NodeList* sel = (*sel_i).second;
            for( NodeList::const_iterator j = sel->begin(); j != sel->end(); j++ ){
              Trace( c ) << *j << " ";
            }
          }
          Trace( c ) << std::endl;
        }
      }
    }
    ++eqcs_i;
  }
}

Node TheoryDatatypes::mkAnd( std::vector< TNode >& assumptions ) {
  if( assumptions.empty() ){
    return NodeManager::currentNM()->mkConst( true );
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( AND, assumptions );
  }
}
