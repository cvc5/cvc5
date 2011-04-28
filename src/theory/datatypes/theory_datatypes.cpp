/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
#include "util/Assert.h"

#include <map>

//#define USE_TRANSITIVE_CLOSURE

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

const Datatype::Constructor& TheoryDatatypes::getConstructor( Node cons )
{
  Expr consExpr = cons.toExpr();
  return Datatype::datatypeOf(consExpr)[ Datatype::indexOf(consExpr) ];
}

Node TheoryDatatypes::getConstructorForSelector( Node sel )
{
  size_t selIndex = Datatype::indexOf( sel.toExpr() );
  const Datatype& dt = ((DatatypeType)((sel.getType()[0]).toType())).getDatatype();
  for( unsigned i = 0; i<dt.getNumConstructors(); i++ ){
    if( dt[i].getNumArgs()>selIndex && 
        Node::fromExpr( dt[i][selIndex].getSelector() )==sel ){
      return Node::fromExpr( dt[i].getConstructor() );
    }
  }
  Assert( false );
  return Node::null();
}


TheoryDatatypes::TheoryDatatypes(Context* c, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_DATATYPES, c, out, valuation),
  d_currAsserts(c),
  d_currEqualities(c),
  d_drv_map(c),
  d_axioms(c),
  d_selectors(c),
  d_reps(c),
  d_selector_eq(c),
  d_equivalence_class(c),
  d_inst_map(c),
  d_cycle_check(c),
  d_hasSeenCycle(c, false),
  d_labels(c),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_disequalities(c),
  d_equalities(c),
  d_conflict(),
  d_noMerge(false),
  d_inCheck(false){

  ////bug test for transitive closure
  //TransitiveClosure tc( c );
  //Debug("datatypes-tc") << "1 -> 0 : " << tc.addEdge( 1, 0 ) << std::endl;
  //Debug("datatypes-tc") << "32 -> 1 : " << tc.addEdge( 32, 1 ) << std::endl;
  //tc.debugPrintMatrix();
}


TheoryDatatypes::~TheoryDatatypes() {
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                     << t << endl;
}


void TheoryDatatypes::notifyEq(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyEq(): "
                     << lhs << " = " << rhs << endl;
  //if(!d_conflict.isNull()) {
  //  return;
  //}
  //merge(lhs,rhs);
  //FIXME
  //Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, lhs, rhs);
  //addEquality(eq);
  //d_drv_map[eq] = d_cc.explain( lhs, rhs );
}

void TheoryDatatypes::notifyCongruent(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyCongruent(): "
                     << lhs << " = " << rhs << endl;
  if(d_conflict.isNull()) {
    merge(lhs,rhs);
  }
  Debug("datatypes-debug") << "TheoryDatatypes::notifyCongruent(): done." << endl;
}

void TheoryDatatypes::preRegisterTerm(TNode n) {  
  Debug("datatypes-prereg") << "TheoryDatatypes::preRegisterTerm() " << n << endl;
}


void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
}

void TheoryDatatypes::check(Effort e) {

  for( int i=0; i<(int)d_currAsserts.size(); i++ ) {
    Debug("datatypes") << "currAsserts[" << i << "] = " << d_currAsserts[i] << endl;
  }
  for( int i=0; i<(int)d_currEqualities.size(); i++ ) {
    Debug("datatypes") << "currEqualities[" << i << "] = " << d_currEqualities[i] << endl;
  }

  while(!done()) {
    Node assertion = get();
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") || Debug.isOn("datatypes-cycles") ) {
      cout << "*** TheoryDatatypes::check(): " << assertion << endl;
      d_currAsserts.push_back( assertion );
    }

    //clear from the derived map
    d_inCheck = true;
    collectTerms( assertion );
    if( d_conflict.isNull() ){
      if( !d_drv_map[assertion].get().isNull() ) {
        Debug("datatypes") << "Assertion has already been derived" << endl;
        d_drv_map[assertion] = Node::null();
      } else {
        switch(assertion.getKind()) {
        case kind::EQUAL:
        case kind::IFF:
          addEquality(assertion);
          break;
        case kind::APPLY_TESTER:
          checkTester( assertion );
          break;
        case kind::NOT:
          {
            switch( assertion[0].getKind()) {
            case kind::EQUAL:
            case kind::IFF:
              {
                Node a = assertion[0][0];
                Node b = assertion[0][1];
                addDisequality(assertion[0]);
                d_cc.addTerm(a);
                d_cc.addTerm(b);
                if(Debug.isOn("datatypes")) {
                  Debug("datatypes") << "       a  == > " << a << endl
                              << "       b  == > " << b << endl
                              << "  find(a) == > " << debugFind(a) << endl
                              << "  find(b) == > " << debugFind(b) << endl;
                }
                // There are two ways to get a conflict here.
                if(d_conflict.isNull()) {
                  if(find(a) == find(b)) {
                    // We get a conflict this way if we WERE previously watching
                    // a, b and were notified previously (via notifyCongruent())
                    // that they were congruent.
                    NodeBuilder<> nb(kind::AND);
                    nb << d_cc.explain( assertion[0][0], assertion[0][1] );
                    nb << assertion;
                    d_conflict = nb;
                    Debug("datatypes") << "Disequality conflict " << d_conflict << endl;
                  } else {
                    // If we get this far, there should be nothing conflicting due
                    // to this disequality.
                    Assert(!d_cc.areCongruent(a, b));
                  }
                }
              }
              break;
            case kind::APPLY_TESTER:
              checkTester( assertion );
              break;
            default:
              Unhandled(assertion[0].getKind());
              break;
            }
          }
          break;
        default:
          Unhandled(assertion.getKind());
          break;
        }
      }
    }
    d_inCheck = false;
    if(!d_conflict.isNull()) {
      throwConflict();
      return;
    }
  }

  if( e == FULL_EFFORT ) {
    Debug("datatypes-split") << "Check for splits " << e << endl;
    //do splitting
    for( EqLists::iterator i = d_labels.begin(); i != d_labels.end(); i++ ) {
      Node sf = find( (*i).first );
      if( sf == (*i).first || sf.getKind() != APPLY_CONSTRUCTOR ) {
        EqList* lbl = (sf == (*i).first) ? (*i).second : (*d_labels.find( sf )).second;
        Debug("datatypes-split") << "Check for splitting " << (*i).first << ", ";
        Debug("datatypes-split") << "label size = " << lbl->size() << endl;
        Node cons = getPossibleCons( (*i).first, false );
        if( !cons.isNull() ) {
          const Datatype::Constructor& cn = getConstructor( cons );
          Debug("datatypes-split") << "*************Split for possible constructor " << cons << endl;
          Node test = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), (*i).first );
          NodeBuilder<> nb(kind::OR);
          nb << test << test.notNode();
          Node lemma = nb;
          Debug("datatypes-split") << "Lemma is " << lemma << endl;
          d_out->lemma( lemma );
          return;
        }
      } else {
        Debug("datatypes-split") << (*i).first << " is " << sf << endl;
      }
    }
  }
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ) {
    cout << "TheoryDatatypes::check(): done" << endl;
  }
}

void TheoryDatatypes::checkTester( Node assertion, bool doAdd ) {
  Debug("datatypes") << "Check tester " << assertion << endl;

  Node tassertion = ( assertion.getKind() == NOT ) ? assertion[0] : assertion;
  const Datatype& dt = Datatype::datatypeOf( tassertion.getOperator().toExpr() );

  //add the term into congruence closure consideration
  d_cc.addTerm( tassertion[0] );

  Node assertionRep = assertion;
  Node tassertionRep = tassertion;
  Node tRep = tassertion[0];
  //tRep = collapseSelector( tRep, Node::null(), true );
  tRep = find( tRep );
  Debug("datatypes") << "tRep is " << tRep << " " << tassertion[0] << endl;
  //add label instead for the representative (if it is different)
  if( tRep != tassertion[0] ) {
    tassertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, tassertion.getOperator(), tRep );
    assertionRep = ( assertion.getKind() == NOT ) ? tassertionRep.notNode() : tassertionRep;
    //add explanation
    if( doAdd ) {
      Node explanation = d_cc.explain( tRep, tassertion[0] );
      NodeBuilder<> nb(kind::AND);
      nb << explanation << assertion;
      explanation = nb;
      Debug("datatypes-drv") << "Check derived tester " << assertionRep << endl;
      Debug("datatypes-drv") << "  Justification is " << explanation << endl;
      d_drv_map[assertionRep] = explanation;
    }
  }

  //if tRep is a constructor, it is trivial
  if( tRep.getKind() == APPLY_CONSTRUCTOR ) {
    if( checkTrivialTester( tassertionRep ) == (assertionRep.getKind() == NOT) ) {
      d_conflict = doAdd ? assertionRep : NodeManager::currentNM()->mkConst(true);
      Debug("datatypes") << "Trivial conflict " << assertionRep << endl;
    }
    return;
  }

  addTermToLabels( tRep );
  EqLists::iterator lbl_i = d_labels.find(tRep);
  //Debug("datatypes") << "Found " << (lbl_i == d_labels.end()) << endl;
  Assert( lbl_i != d_labels.end() );

  EqList* lbl = (*lbl_i).second;
  //Debug("datatypes") << "Check lbl = " << lbl << ", size = " << lbl->size() << endl;

  //check if empty label (no possible constructors for term)
  bool add = true;
  unsigned int notCount = 0;
  if( !lbl->empty() ) {
    for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
      Node leqn = (*i);
      if( leqn.getKind() == kind::NOT ) {
        if( leqn[0].getOperator() == tassertionRep.getOperator() ) {
          if( assertionRep.getKind() == NOT ) {
            add = false;
          } else {
            NodeBuilder<> nb(kind::AND);
            nb << leqn;
            if( doAdd ) nb << assertionRep;
            d_conflict = nb.getNumChildren() == 1 ? nb.getChild( 0 ) : nb;
            Debug("datatypes") << "Contradictory labels " << d_conflict << endl;
            return;
          }
          break;
        }
        notCount++;
      } else {
        if( (leqn.getOperator() == tassertionRep.getOperator()) == (assertionRep.getKind() == NOT) ) {
          NodeBuilder<> nb(kind::AND);
          nb << leqn;
          if( doAdd ) nb << assertionRep;
          d_conflict = nb.getNumChildren() == 1 ? nb.getChild( 0 ) : nb;
          Debug("datatypes") << "Contradictory labels(2) " << d_conflict << endl;
          return;
        }
        add = false;
        break;
      }
    }
  }
  if( add ) {
    if( assertionRep.getKind() == NOT && notCount == dt.getNumConstructors()-1 ) {
      NodeBuilder<> nb(kind::AND);
      if( !lbl->empty() ) {
        for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
          nb << (*i);
        }
      }
      if( doAdd ) nb << assertionRep;
      d_conflict = nb.getNumChildren() == 1 ? nb.getChild( 0 ) : nb;
      Debug("datatypes") << "Exhausted possibilities for labels " << d_conflict << endl;
      return;
    }
    if( doAdd ) {
      lbl->push_back( assertionRep );
      Debug("datatypes") << "Add to labels " << lbl->size() << endl;
    }
  }
  if( doAdd ) {
    checkInstantiate( tRep );
    if( !d_conflict.isNull() ) {
      return;
    }
    //inspect selectors
    updateSelectors( tRep );
  }
  return;
}

bool TheoryDatatypes::checkTrivialTester(Node assertion) {
  AssertArgument(assertion.getKind() == APPLY_TESTER &&
                 assertion[0].getKind() == APPLY_CONSTRUCTOR,
                 assertion, "argument must be a tester-over-constructor");
  TNode tester = assertion.getOperator();
  TNode ctor = assertion[0].getOperator();
  // if they have the same index (and the node has passed
  // typechecking) then this is a trivial tester
  return Datatype::indexOf(tester.toExpr()) == Datatype::indexOf(ctor.toExpr());
}

void TheoryDatatypes::checkInstantiate( Node t ) {
  Debug("datatypes") << "TheoryDatatypes::checkInstantiate() " << t << endl;
  Assert( t == find( t ) );

  //if labels were created for t, and t has not been instantiated
  if( t.getKind() != APPLY_CONSTRUCTOR ) {
    //for each term in equivalance class
    initializeEqClass( t );
    EqListN* eqc = (*d_equivalence_class.find( t )).second;
    for( EqListN::const_iterator iter = eqc->begin(); iter != eqc->end(); iter++ ) {
      Node te = *iter;
      Assert( find( te ) == t );
      if( d_inst_map.find( te ) == d_inst_map.end() ) {
        Node cons = getPossibleCons( te, true );
        EqLists::iterator lbl_i = d_labels.find( t );
        //there is one remaining constructor
        if( !cons.isNull() && lbl_i != d_labels.end() ) {
          EqList* lbl = (*lbl_i).second;
          const Datatype::Constructor& cn = Datatype::datatypeOf( cons.toExpr() )[ Datatype::indexOf( cons.toExpr() ) ];

          //only one constructor possible for term (label is singleton), apply instantiation rule
          //find if selectors have been applied to t
          vector< Node > selectorVals;
          selectorVals.push_back( cons );
          NodeBuilder<> justifyEq(kind::AND);
          bool foundSel = false;
          for( unsigned int i=0; i<cn.getNumArgs(); i++ ) {
            Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( cn[i].getSelector() ), te );
            Debug("datatypes") << "Selector[" << i << "] = " << s << endl;
            if( d_selectors.find( s ) != d_selectors.end() ) {
              Node sf = find( s );
              if( sf != s && sf.getKind() != SKOLEM ) {
                justifyEq << d_cc.explain( sf, s );
              }
              foundSel = true;
              s = sf;
            }
            selectorVals.push_back( s );
          }
          if( cn.isFinite() || foundSel ) {
            d_inst_map[ te ] = true;
            //instantiate, add equality
            Node val = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, selectorVals );
            if( find( val ) != find( te ) ) {
              Node newEq = NodeManager::currentNM()->mkNode( EQUAL, val, te );
              Debug("datatypes") << "Instantiate Equal: " << newEq << "." << endl;
              if( lbl->size() == 1 || (*lbl)[ lbl->size()-1 ].getKind() != NOT ) {
                justifyEq << (*lbl)[ lbl->size()-1 ];
              } else {
                if( !lbl->empty() ) {
                  for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
                    justifyEq << (*i);
                  }
                }
              }
              Node jeq = ( justifyEq.getNumChildren() == 1 ) ? justifyEq.getChild( 0 ) : justifyEq;
              Debug("datatypes-split") << "Instantiate " << newEq << endl;
              preRegisterTerm( val );
              addDerivedEquality( newEq, jeq );
              return;
            }
          } else {
            Debug("datatypes") << "infinite constructor, no selectors " << cons << endl;
          }
        }
      }
    }
  }
}

//checkInst = true is for checkInstantiate, checkInst = false is for splitting
Node TheoryDatatypes::getPossibleCons( Node t, bool checkInst ) {
  Node tf = find( t );
  EqLists::iterator lbl_i = d_labels.find( tf );
  if( lbl_i != d_labels.end() ) {
    EqList* lbl = (*lbl_i).second;
    TypeNode typ = t.getType();

    const Datatype& dt = ((DatatypeType)typ.toType()).getDatatype();

    //if ended by one positive tester
    if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind() != NOT ) {
      if( checkInst ) {
        size_t testerIndex = Datatype::indexOf( (*lbl)[ lbl->size()-1 ].getOperator().toExpr() );
        return Node::fromExpr( dt[ testerIndex ].getConstructor() );
      }
    //if (n-1) negative testers
    } else if( !checkInst || lbl->size() == dt.getNumConstructors()-1 ) {
      vector< bool > possibleCons;
      possibleCons.resize( dt.getNumConstructors(), true );
      if( !lbl->empty() ) {
        for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
          TNode leqn = (*i);
          possibleCons[ Datatype::indexOf( leqn[0].getOperator().toExpr() ) ] = false;
        }
      }
      Node cons = Node::null();
      for( unsigned int i=0; i<possibleCons.size(); i++ ) {
        if( possibleCons[i] ) {
          cons = Node::fromExpr( dt[ i ].getConstructor() );
          if( !checkInst ) {
            //if there is a selector, split
            for( unsigned int j=0; j<dt[ i ].getNumArgs(); j++ ) {
              Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[i][j].getSelector() ), tf );
              if( d_selectors.find( s ) != d_selectors.end() ) {
                Debug("datatypes") << "  getPosCons: found selector " << s << endl;
                return cons;
              }
            }
          }
        }
      }
      if( !checkInst ) {
        for( int i=0; i<(int)possibleCons.size(); i++ ) {
          if( possibleCons[i] && !dt[ i ].isFinite() ) {
            Debug("datatypes") << "Did not find selector for " << tf;
            Debug("datatypes") << " and " << dt[ i ].getConstructor() << " is not finite." << endl;
            return Node::null();
          }
        }
      } else {
        Assert( !cons.isNull() );
      }
      return cons;
    }
  }
  return Node::null();
}

Node TheoryDatatypes::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryDatatypes::merge(TNode a, TNode b) {
  if( d_noMerge ) {
    //Debug("datatypes") << "Append to merge pending list " << d_merge_pending.size() << endl;
    d_merge_pending[d_merge_pending.size()-1].push_back( pair< Node, Node >( a, b ) );
    return;
  }
  Assert(d_conflict.isNull());
  a = find(a);
  b = find(b);
  if( a == b) {
    return;
  }
  Debug("datatypes-cycles") << "Merge "<< a << " " << b << endl;

  // make "a" the one with shorter diseqList
  EqLists::iterator deq_ia = d_disequalities.find(a);
  EqLists::iterator deq_ib = d_disequalities.find(b);

  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
    }
  }

  //if b is a selector, swap a and b
  if( b.getKind() == APPLY_SELECTOR && a.getKind() != APPLY_SELECTOR ) {
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  //make constructors the representatives
  if( a.getKind() == APPLY_CONSTRUCTOR ) {
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  //make sure skolem variable is not representative
  if( b.getKind() == SKOLEM ) {
    TNode tmp = a;
    a = b;
    b = tmp;
  }

  //check for clash
  NodeBuilder<> explanation(kind::AND);
  if( a.getKind() == kind::APPLY_CONSTRUCTOR && b.getKind() == kind::APPLY_CONSTRUCTOR 
      && a.getOperator()!=b.getOperator() ){
    explanation << d_cc.explain( a, b );
    d_conflict = explanation.getNumChildren() == 1 ? explanation.getChild( 0 ) : explanation;
    Debug("datatypes") << "Clash " << a << " " << b << endl;
    Debug("datatypes") << "Conflict is " << d_conflict << endl;
    return; 
  }
  Debug("datatypes-debug") << "Done clash" << endl;

  Debug("datatypes") << "Set canon: "<< a << " " << b << endl;
  // b becomes the canon of a
  d_unionFind.setCanon(a, b);
  d_reps[a] = false;
  d_reps[b] = true;
#ifdef USE_TRANSITIVE_CLOSURE
  bool result = d_cycle_check.addEdgeNode( a, b );
  d_hasSeenCycle.set( d_hasSeenCycle.get() || result );
#endif

  //merge equivalence classes
  initializeEqClass( a );
  initializeEqClass( b );
  EqListN* eqc_a = (*d_equivalence_class.find( a )).second;
  EqListN* eqc_b = (*d_equivalence_class.find( b )).second;
  for( EqListN::const_iterator i = eqc_a->begin(); i != eqc_a->end(); i++ ) {
    eqc_b->push_back( *i );
  }

  deq_ia = d_disequalities.find(a);
  map<TNode, TNode> alreadyDiseqs;
  if(deq_ia != d_disequalities.end()) {
    /*
     * Collecting the disequalities of b, no need to check for conflicts
     * since the representative of b does not change and we check all the things
     * in a's class when we look at the diseq list of find(a)
     */

    EqLists::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      EqList* deq = (*deq_ib).second;
      for(EqList::const_iterator j = deq->begin(); j != deq->end(); j++) {
        TNode deqn = *j;
        TNode s = deqn[0];
        TNode t = deqn[1];
        TNode sp = find(s);
        TNode tp = find(t);
        Assert(sp == b || tp == b, "test1");
        if(sp == b) {
          alreadyDiseqs[tp] = deqn;
        } else {
          alreadyDiseqs[sp] = deqn;
        }
      }
    }

    /*
     * Looking for conflicts in the a disequality list. Note
     * that at this point a and b are already merged. Also has
     * the side effect that it adds them to the list of b (which
     * became the canonical representative)
     */

    EqList* deqa = (*deq_ia).second;
    for(EqList::const_iterator i = deqa->begin(); i != deqa->end(); i++) {
      TNode deqn = (*i);
      Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];

      TNode sp = find(s);
      TNode tp = find(t);
      if(sp == tp) {
        Debug("datatypes") << "Construct standard conflict " << deqn << " " << sp << endl;
        Node explanation = d_cc.explain(deqn[0], deqn[1]);
        d_conflict = NodeManager::currentNM()->mkNode( kind::AND, explanation, deqn.notNode() );
        Debug("datatypes") << "Conflict is " << d_conflict << endl;
        return;
      }
      Assert( sp == b || tp == b, "test2");

      // make sure not to add duplicates

      if(sp == b) {
        if(alreadyDiseqs.find(tp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[tp] = deqn;
        }
      } else {
        if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[sp] = deqn;
        }
      }

    }
  }

  //Debug("datatypes-debug") << "Done clash" << endl;
#ifdef USE_TRANSITIVE_CLOSURE
  Debug("datatypes-cycles") << "Equal " << a << " -> " << b << " " << d_hasSeenCycle.get() << endl;
  if( d_hasSeenCycle.get() ){
    checkCycles();
    if( !d_conflict.isNull() ){
      return;
    }
  }else{
    checkCycles();
    if( !d_conflict.isNull() ){
      Debug("datatypes-cycles") << "Cycle is " << d_conflict << std::endl;
      for( int i=0; i<(int)d_currEqualities.size(); i++ ) {
        Debug("datatypes-cycles") << "currEqualities[" << i << "] = " << d_currEqualities[i] << endl;
      }
      d_cycle_check.debugPrint();
      Assert( false );
    }
  }
#else
  checkCycles();
  if( !d_conflict.isNull() ){
    return;
  }
#endif
  Debug("datatypes-debug") << "Done cycles" << endl;

  //merge selector lists
  updateSelectors( a );
  if( !d_conflict.isNull() ){
    return;
  }
  Debug("datatypes-debug") << "Done collapse" << endl;

  //merge labels
  EqLists::iterator lbl_i = d_labels.find( a );
  if(lbl_i != d_labels.end()) {
    EqList* lbl = (*lbl_i).second;
    if( !lbl->empty() ) {
      for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
        checkTester( *i );
        if( !d_conflict.isNull() ) {
          return;
        }
      }
    }
  }
  Debug("datatypes-debug") << "Done merge labels" << endl;

  //do unification
  Assert( d_conflict.isNull() );
  if( a.getKind() == APPLY_CONSTRUCTOR && b.getKind() == APPLY_CONSTRUCTOR &&
      a.getOperator() == b.getOperator() ) {
    Debug("datatypes") << "Unification: " << a << " and " << b << "." << endl;
    for( int i=0; i<(int)a.getNumChildren(); i++ ) {
      if( find( a[i] ) != find( b[i] ) ) {
        Node newEq = NodeManager::currentNM()->mkNode( EQUAL, a[i], b[i] );
        Node jEq = d_cc.explain(a, b);
        addDerivedEquality( newEq, jEq );
      }
    }
  }

  Debug("datatypes-debug") << "merge(): Done" << endl;
}

Node TheoryDatatypes::collapseSelector( TNode t, bool useContext ) {
  if( t.getKind() == APPLY_SELECTOR ) {
    //collapse constructor
    TypeNode typ = t[0].getType();
    Node sel = t.getOperator();
    TypeNode selType = sel.getType();
    Node cons = getConstructorForSelector( sel );
    const Datatype::Constructor& cn = getConstructor( cons );
    Node tmp = find( t[0] );
    Node retNode = t;
    if( tmp.getKind() == APPLY_CONSTRUCTOR ) {
      if( tmp.getOperator() == cons ) {
        size_t selIndex = Datatype::indexOf( sel.toExpr() );
        Debug("datatypes") << "Applied selector " << t << " to correct constructor, index = " << selIndex << endl;
        Debug("datatypes") << "Return " << tmp[selIndex] << endl;
        retNode = tmp[selIndex];
      } else {
        Debug("datatypes") << "Applied selector " << t << " to wrong constructor " << endl;
        Debug("datatypes") << "Return distinguished term ";
        Debug("datatypes") << selType[1].mkGroundTerm() << " of type " << selType[1] << endl;
        retNode = selType[1].mkGroundTerm();
      }
      if( useContext ) {
        Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );
        d_axioms[neq] = true;
        Debug("datatypes-split") << "Collapse selector " << neq << endl;
        addEquality( neq );
      }
    } else {
      if( useContext ) {
        //check labels
        Node tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), tmp );
        checkTester( tester, false );
        if( !d_conflict.isNull() ) {
          Debug("datatypes") << "Applied selector " << t << " to provably wrong constructor." << endl;
          retNode = selType[1].mkGroundTerm();

          Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );
          NodeBuilder<> nb(kind::AND);
          Node trueNode = NodeManager::currentNM()->mkConst(true);
          if( d_conflict != trueNode ) {
            nb << d_conflict;
          }
          d_conflict = Node::null();
          tmp = find( tmp );
          if( tmp != t[0] ) {
            nb << d_cc.explain( tmp, t[0] );
          }
          Assert( nb.getNumChildren()>0 );
          Node jEq = nb.getNumChildren() == 1 ? nb.getChild( 0 ) : nb;
          Debug("datatypes-drv") << "Collapse selector " << neq << endl;
          addDerivedEquality( neq, jEq );
        }
      }
    }
    return retNode;
  }
  return t;
}

void TheoryDatatypes::updateSelectors( Node a ) {
  EqListsN::iterator sel_a_i = d_selector_eq.find( a );
  if( sel_a_i != d_selector_eq.end() ) {
    EqListN* sel_a = (*sel_a_i).second;
    Debug("datatypes") << a << " has " << sel_a->size() << " selectors" << endl;
    if( !sel_a->empty() ) {
      EqListN* sel_b = NULL;
      for( EqListN::const_iterator i = sel_a->begin(); i != sel_a->end(); i++ ) {
        Node s = (*i);
        Node b = find( a );
        if( b != a ) {
          EqListsN::iterator sel_b_i = d_selector_eq.find( b );
          if( sel_b_i == d_selector_eq.end() ) {
            sel_b = new(getContext()->getCMM()) EqListN(true, getContext(), false,
                                                  ContextMemoryAllocator<Node>(getContext()->getCMM()));
            d_selector_eq.insertDataFromContextMemory(b, sel_b);
          } else {
            sel_b = (*sel_b_i).second;
          }
          a = b;
        }
        Debug("datatypes") << "Merge selector " << s << " into " << b << endl;
        Debug("datatypes") << "Find is " << find( s[0] ) << endl;
        Assert( s.getKind() == APPLY_SELECTOR &&
                find( s[0] ) == b );
        if( b != s[0] ) {
          Node t = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, s.getOperator(), b );
          //add to labels
          addTermToLabels( t );
          merge( s, t );
          s = t;
          d_selectors[s] = true;
          d_cc.addTerm( s );
        }
        s = collapseSelector( s, true );
        if( !d_conflict.isNull() ) {
          return;
        }
        if( sel_b && s.getKind() == APPLY_SELECTOR ) {
          sel_b->push_back( s );
        }
      }
    }
  } else {
    Debug("datatypes") << a << " has no selectors" << endl;
  }
}

void TheoryDatatypes::addTermToLabels( Node t ) {
  if( t.getKind() == VARIABLE || t.getKind() == APPLY_SELECTOR ) {
    Node tmp = find( t );
    if( tmp == t ) {
      //add to labels
      EqLists::iterator lbl_i = d_labels.find(t);
      if(lbl_i == d_labels.end()) {
        EqList* lbl = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                                ContextMemoryAllocator<TNode>(getContext()->getCMM()));
        d_labels.insertDataFromContextMemory(tmp, lbl);
      }
    }
  }
}

void TheoryDatatypes::initializeEqClass( Node t ) {
  EqListsN::iterator eqc_i = d_equivalence_class.find( t );
  if( eqc_i == d_equivalence_class.end() ) {
    EqListN* eqc = new(getContext()->getCMM()) EqListN(true, getContext(), false,
                                          ContextMemoryAllocator<Node>(getContext()->getCMM()));
    eqc->push_back( t );
    d_equivalence_class.insertDataFromContextMemory(t, eqc);
  }
}

void TheoryDatatypes::collectTerms( Node n ) {
  for( int i=0; i<(int)n.getNumChildren(); i++ ) {
    collectTerms( n[i] );
  }
  if( n.getKind() == APPLY_CONSTRUCTOR ){
#ifdef USE_TRANSITIVE_CLOSURE
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      Debug("datatypes-cycles") << "Subterm " << n << " -> " << n[i] << endl;
      bool result = d_cycle_check.addEdgeNode( n, n[i] );
      //if( result ){
      //  for( int i=0; i<(int)d_currEqualities.size(); i++ ) {
      //    Debug("datatypes-cycles") << "currEqualities[" << i << "] = " << d_currEqualities[i] << endl;
      //  }
      //  d_cycle_check.debugPrint();
      //}
      Assert( !result );    //this should not create any new cycles (relevant terms should have been recorded before)
    }
#endif
  }
  if( n.getKind() == APPLY_SELECTOR ) {
    if( d_selectors.find( n ) == d_selectors.end() ) {
      Debug("datatypes-split") << "  Found selector " << n << endl;
      d_selectors[ n ] = true;
      d_cc.addTerm( n );
      Node tmp = find( n[0] );
      checkInstantiate( tmp );

      Node s = n;
      if( tmp != n[0] ) {
        s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, n.getOperator(), tmp );
      }
      Debug("datatypes-split") << "  Before collapse: " << s << endl;
      s = collapseSelector( s, true );
      Debug("datatypes-split") << "  After collapse: " << s << endl;
      if( s.getKind() == APPLY_SELECTOR ) {
        //add selector to selector eq list
        Debug("datatypes") << "  Add selector to list " << tmp << " " << n << endl;
        EqListsN::iterator sel_i = d_selector_eq.find( tmp );
        EqListN* sel;
        if( sel_i == d_selector_eq.end() ) {
          sel = new(getContext()->getCMM()) EqListN(true, getContext(), false,
                                            ContextMemoryAllocator<Node>(getContext()->getCMM()));
          d_selector_eq.insertDataFromContextMemory(tmp, sel);
        } else {
          sel = (*sel_i).second;
        }
        sel->push_back( s );
      } else {
        Debug("datatypes") << "  collapsed selector to " << s << endl;
      }
    }
  }
  addTermToLabels( n );
}

void TheoryDatatypes::appendToDiseqList(TNode of, TNode eq) {
  Debug("datatypes") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator deq_i = d_disequalities.find(of);
  EqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  //if(Debug.isOn("uf")) {
  //  Debug("uf") << "  size is now " << deq->size() << endl;
  //}
}

void TheoryDatatypes::addDerivedEquality(TNode eq, TNode jeq) {
  Debug("datatypes-drv") << "Justification for " << eq << "is: " << jeq << "." << endl;
  d_drv_map[eq] = jeq;
  addEquality( eq );
}

void TheoryDatatypes::addEquality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  if( eq[0] != eq[1] ) {
    Debug("datatypes") << "Add equality " << eq << "." << endl;

    //setup merge pending list
    d_merge_pending.push_back( vector< pair< Node, Node > >() );
    bool prevNoMerge = d_noMerge;
    d_noMerge = true;

    d_cc.addTerm(eq[0]);
    d_cc.addTerm(eq[1]);
    d_cc.addEquality(eq);
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-cycles") ){
      d_currEqualities.push_back(eq);
    }

    //record which nodes are waiting to be merged
    d_noMerge = prevNoMerge;
    vector< pair< Node, Node > > mp;
    mp.insert( mp.begin(), 
               d_merge_pending[d_merge_pending.size()-1].begin(), 
               d_merge_pending[d_merge_pending.size()-1].end() );
    d_merge_pending.pop_back();

    //merge original nodes
    if( d_conflict.isNull() ) {
      merge(eq[0], eq[1]);
    }
    //merge nodes waiting to be merged
    for( int i=0; i<(int)mp.size(); i++ ) {
      if( d_conflict.isNull() ) {
        merge( mp[i].first, mp[i].second );
      }
    }
  }
}

void TheoryDatatypes::addDisequality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  TNode a = eq[0];
  TNode b = eq[1];

  appendToDiseqList(find(a), eq);
  appendToDiseqList(find(b), eq);
}

void TheoryDatatypes::throwConflict() {
  Debug("datatypes") << "Convert conflict : " << d_conflict << endl;
  NodeBuilder<> nb(kind::AND);
  convertDerived( d_conflict, nb );
  d_conflict = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") || Debug.isOn("datatypes-cycles") ) {
    cout << "Conflict constructed : " << d_conflict << endl;
  }
  //if( d_conflict.getKind()!=kind::AND ){
  //  d_conflict = NodeManager::currentNM()->mkNode(kind::AND, d_conflict, d_conflict);
  //}
  d_out->conflict( d_conflict, false );
  d_conflict = Node::null();
}

void TheoryDatatypes::convertDerived(Node n, NodeBuilder<>& nb) {
  if( n.getKind() == kind::AND ) {
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      convertDerived( n[i], nb );
    }
  } else if( !d_drv_map[ n ].get().isNull() ) {
    //Debug("datatypes") << "Justification for " << n << " is " << d_drv_map[ n ].get() << endl;
    convertDerived( d_drv_map[ n ].get(), nb );
  } else if( d_axioms.find( n ) == d_axioms.end() ) {
    nb << n;
  }
}

void TheoryDatatypes::checkCycles() {
  for( BoolMap::iterator i = d_reps.begin(); i != d_reps.end(); i++ ) {
    if( (*i).second ) {
      map< Node, bool > visited;
      NodeBuilder<> explanation(kind::AND);
      if( searchForCycle( (*i).first, (*i).first, visited, explanation ) ) {
        Assert( explanation.getNumChildren()>0 );
        d_conflict = explanation.getNumChildren() == 1 ? explanation.getChild( 0 ) : explanation;
        Debug("datatypes") << "Detected cycle for " << (*i).first << endl;
        Debug("datatypes") << "Conflict is " << d_conflict << endl;
        return;
      }
    }
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
bool TheoryDatatypes::searchForCycle( Node n, Node on,
                                      map< Node, bool >& visited,
                                      NodeBuilder<>& explanation ) {
  //Debug("datatypes") << "Search for cycle " << n << " " << on << endl;
  if( n.getKind() == APPLY_CONSTRUCTOR ) {
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      Node nn = find( n[i] );
      if( visited.find( nn ) == visited.end() ) {
        visited[nn] = true;
        if( nn == on || searchForCycle( nn, on, visited, explanation ) ) {
          if( !d_cycle_check.isConnectedNode( n, n[i] ) ){
            Debug("datatypes-cycles") << "Cycle subterm: " << n << " is not -> " << n[i] << "!!!!" << std::endl;
          }
          if( nn != n[i] ) {
            Node e = d_cc.explain( nn, n[i] );
            if( !d_cycle_check.isConnectedNode( n[i], nn ) ){
              Debug("datatypes-cycles") << "Cycle equality: " << n[i] << " is not -> " << nn << "!!!!" << std::endl;
              Debug("datatypes-cycles") << "Explanation: " << e << std::endl;
              if( e.getKind()==kind::AND ){
                for( int a=0; a<e.getNumChildren(); a++ ){
                  Debug("datatypes-cycles") << e[a][0] << " " << e[a][1] << " "
                    << d_cycle_check.isConnectedNode( e[a][1], e[a][0] ) << " "
                    << d_cycle_check.isConnectedNode( e[a][0], e[a][1] ) << std::endl;
                }
              }
            }
            explanation << e;
          }
          return true;
        }
      }
    }
  }
  return false;
}
