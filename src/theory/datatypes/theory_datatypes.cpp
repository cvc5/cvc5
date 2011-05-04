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
  d_noMerge(false),
  d_inCheck(false),
  d_em(c),
  d_cce(&d_cc){

  ////bug test for transitive closure
  //TransitiveClosure tc( c );
  //Debug("datatypes-tc") << "33 -> 32 : " << tc.addEdge( 33, 32 ) << std::endl;
  //Debug("datatypes-tc") << "32 -> 33 : " << tc.addEdge( 32, 33 ) << std::endl;
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
  
}

void TheoryDatatypes::notifyCongruent(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyCongruent(): "
                     << lhs << " = " << rhs << endl;
  if(!hasConflict()) {
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
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") || Debug.isOn("datatypes-cycles")
        || Debug.isOn("datatypes-debug-pf") ) {
      cout << "*** TheoryDatatypes::check(): " << assertion << endl;
      d_currAsserts.push_back( assertion );
    }

    //clear from the derived map
    d_inCheck = true;
    collectTerms( assertion );
    if( !hasConflict() ){
      if( d_em.hasNode( assertion ) ){
        Debug("datatypes") << "Assertion has already been derived" << endl;
        d_em.assert( assertion );
      } else {
        switch(assertion.getKind()) {
        case kind::EQUAL:
        case kind::IFF:
          addEquality(assertion);
          break;
        case kind::APPLY_TESTER:
          addTester( assertion );
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
                if(!hasConflict()) {
                  if(find(a) == find(b)) {
                    // We get a conflict this way if we WERE previously watching
                    // a, b and were notified previously (via notifyCongruent())
                    // that they were congruent.
                    Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, assertion[0][0], assertion[0][1] );
                    NodeBuilder<> nbc(kind::AND);
                    nbc << ccEq << assertion;
                    Node contra = nbc;
                    d_em.addNode( ccEq, &d_cce );
                    d_em.addNodeConflict( contra, Reason::contradiction );
                  } else {
                    // If we get this far, there should be nothing conflicting due
                    // to this disequality.
                    Assert(!d_cc.areCongruent(a, b));
                  }
                }
              }
              break;
            case kind::APPLY_TESTER:
              addTester( assertion );
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
    Debug("datatypes-debug-pf") << "Done check " << assertion << " " << hasConflict() << std::endl;
    d_inCheck = false;
    if( hasConflict() ) {
      Debug("datatypes-conflict") << "Constructing conflict..." << endl;
      Debug("datatypes-conflict") << d_cc << std::endl;
      Node conflict = d_em.getConflict();
      if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") || 
          Debug.isOn("datatypes-cycles") || Debug.isOn("datatypes-conflict") ){
        cout << "Conflict constructed : " << conflict << endl;
      }
      //if( conflict.getKind()!=kind::AND ){
      //  conflict = NodeManager::currentNM()->mkNode(kind::AND, conflict, conflict);
      //}
      d_out->conflict( conflict, false );
      //Assert( false );
      return;
    }
  }

  if( e == FULL_EFFORT ) {
    Debug("datatypes-split") << "Check for splits " << e << endl;
    //do splitting
    for( EqLists::iterator i = d_labels.begin(); i != d_labels.end(); i++ ) {
      Node sf = find( (*i).first );
      if( sf == (*i).first || sf.getKind() != APPLY_CONSTRUCTOR ) {
        addTermToLabels( sf );
        EqList* lbl = (sf == (*i).first) ? (*i).second : (*d_labels.find( sf )).second;
        Debug("datatypes-split") << "Check for splitting " << (*i).first
                                 << ", label size = " << lbl->size() << endl;
        if( lbl->empty() || (*lbl)[ lbl->size()-1 ].getKind() == NOT ) {
          TypeNode typ = sf.getType();
          const Datatype& dt = ((DatatypeType)typ.toType()).getDatatype();
          vector< bool > possibleCons;
          possibleCons.resize( dt.getNumConstructors(), true );
          for( EqList::const_iterator j = lbl->begin(); j != lbl->end(); j++ ) {
            TNode leqn = (*j);
            possibleCons[ Datatype::indexOf( leqn[0].getOperator().toExpr() ) ] = false;
          }
          Node cons;
          bool foundSel = false;
          for( unsigned int j=0; j<possibleCons.size(); j++ ) {
            if( !foundSel && possibleCons[j] ) {
              cons = Node::fromExpr( dt[ j ].getConstructor() );
              //if there is a selector, split
              for( unsigned int k=0; k<dt[ j ].getNumArgs(); k++ ) {
                Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[j][k].getSelector() ), sf );
                if( d_selectors.find( s ) != d_selectors.end() ) {
                  Debug("datatypes") << "  getPosCons: found selector " << s << endl;
                  foundSel = true;
                  break;
                }
              }
            }
          }
          if( !foundSel ){
            for( unsigned int j=0; j<(int)possibleCons.size(); j++ ) {
              if( possibleCons[j] && !dt[ j ].isFinite() ) {
                Debug("datatypes") << "Did not find selector for " << sf
                                  << " and " << dt[ j ].getConstructor() << " is not finite." << endl;
                cons = Node::null();
                break;
              }
            }
          }
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

bool TheoryDatatypes::checkTester( Node assertion, Node& conflict, unsigned& r ){
  Debug("datatypes") << "Check tester " << assertion << endl;

  //preprocess the tester
  Node tassertion = ( assertion.getKind() == NOT ) ? assertion[0] : assertion;
  Assert( find( tassertion[0] ) == tassertion[0] );

  //if argument is a constructor, it is trivial
  if( tassertion[0].getKind() == APPLY_CONSTRUCTOR ) {
    size_t tIndex = Datatype::indexOf(tassertion.getOperator().toExpr());
    size_t cIndex = Datatype::indexOf(tassertion[0].getOperator().toExpr());
    if( (tIndex==cIndex) == (assertion.getKind() == NOT) ) {
      conflict = assertion;
      r = Reason::idt_tclash;
    }
    return false;
  }

  addTermToLabels( tassertion[0] );
  EqLists::iterator lbl_i = d_labels.find( tassertion[0] );
  EqList* lbl = (*lbl_i).second;
  Assert( !lbl->empty() || lbl->begin()==lbl->end() );
  //check if empty label (no possible constructors for term)
  bool redundant = false;
  for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
    Node leqn = (*i);
    if( leqn.getKind() == kind::NOT ) {
      if( leqn[0].getOperator() == tassertion.getOperator() ) {
        if( assertion.getKind() == NOT ) {
          redundant = true;
        } else {
          conflict = NodeManager::currentNM()->mkNode( AND, leqn, assertion );
          r = Reason::contradiction;
          Debug("datatypes") << "Contradictory labels " << conflict << endl;
          return false;
        }
        break;
      }
    }else{
      if( (leqn.getOperator() == tassertion.getOperator()) == (assertion.getKind() == NOT) ) {
        conflict = NodeManager::currentNM()->mkNode( AND, leqn, assertion );
        r = Reason::idt_tclash;
        Debug("datatypes") << "Contradictory labels(2) " << conflict << endl;
        return false;
      }
      redundant = true;
      break;
    }
  }
  return !redundant;
}

void TheoryDatatypes::addTester( Node assertion ){
  Debug("datatypes") << "Add tester " << assertion << endl;

  //preprocess the tester
  Node tassertion = ( assertion.getKind() == NOT ) ? assertion[0] : assertion;
  //add the term into congruence closure consideration
  d_cc.addTerm( tassertion[0] );

  Node assertionRep;
  Node tassertionRep;
  Node tRep = tassertion[0];
  tRep = find( tRep );
  //add label instead for the representative (if it is different)
  if( tRep != tassertion[0] ) {
    tassertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, tassertion.getOperator(), tRep );
    assertionRep = ( assertion.getKind() == NOT ) ? tassertionRep.notNode() : tassertionRep;
    //add explanation
    Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, tRep, tassertion[0] );
    d_em.addNode( ccEq, &d_cce );
    NodeBuilder<> nb2(kind::AND);
    nb2 << assertion << ccEq;
    Node expl = nb2;
    d_em.addNode( assertionRep, expl, Reason::idt_tcong );
  }else{
    tassertionRep = tassertion;
    assertionRep = assertion;
  }

  Node conflict;
  unsigned r;
  if( checkTester( assertionRep, conflict, r ) ){
    EqLists::iterator lbl_i = d_labels.find( tRep );
    EqList* lbl = (*lbl_i).second;
    lbl->push_back( assertionRep );
    Debug("datatypes") << "Add to labels " << lbl->size() << endl;
    if( assertionRep.getKind()==NOT ){
      const Datatype& dt = Datatype::datatypeOf( tassertion.getOperator().toExpr() );
      //we can conclude the final one
      if( lbl->size()==dt.getNumConstructors()-1 ){
        vector< bool > possibleCons;
        possibleCons.resize( dt.getNumConstructors(), true );
        NodeBuilder<> nb(kind::AND);
        for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
          possibleCons[ Datatype::indexOf( (*i)[0].getOperator().toExpr() ) ] = false;
          nb << (*i);
        }
        unsigned int testerIndex = -1;
        for( unsigned int i=0; i<possibleCons.size(); i++ ) {
          if( possibleCons[i] ){
            Assert( testerIndex==unsigned(-1) );
            testerIndex = i;
          }
        }
        Assert( testerIndex!=unsigned(-1) );
        assertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[testerIndex].getTester() ), tRep );
        Node exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
        d_em.addNode( assertionRep, exp, Reason::idt_texhaust );
        addTester( assertionRep );    //add stronger statement
        return;
      }
    }
    if( assertionRep.getKind()==APPLY_TESTER ){
      //we have concluded that tRep must be a particular tester
      //test all nodes in the equivalence class of tRep for instantiation
      checkInstantiate( tRep );
      if( hasConflict() ) {
        return;
      }
      //update all selectors whose arguments are in the equivalence class of tRep
      updateSelectors( tRep );
    }
  }else if( !conflict.isNull() ){
    d_em.addNodeConflict( conflict, r );
  }
}

void TheoryDatatypes::checkInstantiate( Node t ) {
  Debug("datatypes") << "TheoryDatatypes::checkInstantiate() " << t << endl;
  Assert( t == find( t ) );

  //if labels were created for t, and t has not been instantiated
  if( t.getKind() != APPLY_CONSTRUCTOR ) {
    //for each term in equivalance class
    initializeEqClass( t );
    TypeNode typ = t.getType();
    EqListN* eqc = (*d_equivalence_class.find( t )).second;
    for( EqListN::const_iterator iter = eqc->begin(); iter != eqc->end(); iter++ ) {
      Node te = *iter;
      Assert( find( te ) == t );
      //if term has not yet been instantiated
      if( d_inst_map.find( te ) == d_inst_map.end() ) {
        EqLists::iterator lbl_i = d_labels.find( t );
        if( lbl_i!=d_labels.end() ) {
          EqList* lbl = (*lbl_i).second;
          //check there is one remaining constructor
          const Datatype& dt = ((DatatypeType)typ.toType()).getDatatype();
          Node cons;
          if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind() != NOT ) {
            size_t testerIndex = Datatype::indexOf( (*lbl)[ lbl->size()-1 ].getOperator().toExpr() );
            Node cons = Node::fromExpr( dt[ testerIndex ].getConstructor() );
            const Datatype::Constructor& cn = Datatype::datatypeOf( cons.toExpr() )[ Datatype::indexOf( cons.toExpr() ) ];

            //only one constructor possible for term (label is singleton), apply instantiation rule
            //find if selectors have been applied to t
            vector< Node > selectorVals;
            selectorVals.push_back( cons );
            bool foundSel = false;
            for( unsigned int i=0; i<cn.getNumArgs(); i++ ) {
              Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( cn[i].getSelector() ), te );
              if( d_selectors.find( s ) != d_selectors.end() ) {
                foundSel = true;
                s = find( s );
              }
              selectorVals.push_back( s );
            }
            if( cn.isFinite() || foundSel ) {
              d_inst_map[ te ] = true;
              //instantiate, add equality
              Node val = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, selectorVals );
              if( find( val ) != find( te ) ) {
                collectTerms( val );
                NodeBuilder<> nb(kind::AND);
                nb << (*lbl)[ lbl->size()-1 ];
                for( unsigned int i=0; i<cn.getNumArgs(); i++ ) {
                  Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( cn[i].getSelector() ), te );
                  if( selectorVals[i+1]!=s ){
                    Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, selectorVals[i+1], s );
                    d_em.addNode( ccEq, &d_cce );
                    nb << ccEq;
                  }else{
                    //reflexive for s, if we want fined grained
                  }
                }
                Node jeq = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
                Node newEq = NodeManager::currentNM()->mkNode( EQUAL, val, te );
                Debug("datatypes") << "Instantiate Equal: " << newEq << "." << endl;
                d_em.addNode( newEq, jeq, Reason::idt_inst );
                addEquality( newEq );
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
  Assert(!hasConflict());
  a = find(a);
  b = find(b);
  if( a == b) {
    return;
  }
  Debug("datatypes") << "Merge "<< a << " " << b << endl;

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
    Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, a, b );
    d_em.addNode( ccEq, &d_cce );
    d_em.addNodeConflict( ccEq, Reason::idt_clash );
    Debug("datatypes") << "Clash " << a << " " << b << endl;
    return; 
  }
  Debug("datatypes-debug") << "Done clash" << endl;

  Debug("datatypes-debug-pf") << "Set canon: "<< a << " " << b << endl;
  // b becomes the canon of a
  d_unionFind.setCanon(a, b);
  d_reps[a] = false;
  d_reps[b] = true;
  //add this to the transitive closure module
  bool result = d_cycle_check.addEdgeNode( a, b );
  d_hasSeenCycle.set( d_hasSeenCycle.get() || result );


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
        d_em.addNode( deqn, &d_cce );
        d_em.addNodeConflict( NodeManager::currentNM()->mkNode( kind::AND, deqn, deqn.notNode() ), Reason::contradiction );
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

  Debug("datatypes-cycles") << "Equal " << a << " -> " << b << " " << d_hasSeenCycle.get() << endl;
  if( d_hasSeenCycle.get() ){
    checkCycles();
    if( hasConflict() ){
      return;
    }
  }
  //else{
  //  checkCycles();
  //  if( hasConflict() ){
  //    for( int i=0; i<(int)d_currEqualities.size(); i++ ) {
  //      Debug("datatypes-cycles") << "currEqualities[" << i << "] = " << d_currEqualities[i] << endl;
  //    }
  //    d_cycle_check.debugPrint();
  //    Assert( false );
  //  }
  //}
  Debug("datatypes-debug") << "Done cycles" << endl;

  //merge selector lists
  updateSelectors( a );
  if( hasConflict() ){
    return;
  }
  Debug("datatypes-debug") << "Done collapse" << endl;

  //merge labels
  EqLists::iterator lbl_i = d_labels.find( a );
  if(lbl_i != d_labels.end()) {
    EqList* lbl = (*lbl_i).second;
    if( !lbl->empty() ) {
      for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
        addTester( *i );
        if( hasConflict() ) {
          return;
        }
      }
    }
  }
  Debug("datatypes-debug") << "Done merge labels" << endl;

  //do unification
  if( a.getKind() == APPLY_CONSTRUCTOR && b.getKind() == APPLY_CONSTRUCTOR &&
      a.getOperator() == b.getOperator() ) {
    Debug("datatypes") << "Unification: " << a << " and " << b << "." << endl;
    for( int i=0; i<(int)a.getNumChildren(); i++ ) {
      if( find( a[i] ) != find( b[i] ) ) {
        Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, a, b );
        Node newEq = NodeManager::currentNM()->mkNode( EQUAL, a[i], b[i] );
        d_em.addNode( ccEq, &d_cce );
        d_em.addNode( newEq, ccEq, Reason::idt_unify );
        addEquality( newEq );
      }
    }
  }

  Debug("datatypes-debug") << "merge(): Done" << endl;
}

Node TheoryDatatypes::collapseSelector( Node t ) {
  if( !hasConflict() && t.getKind() == APPLY_SELECTOR ) {
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
      if( tmp!=t[0] ){
        t = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, t.getOperator(), tmp );
      }
      Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );
      d_em.addNodeAxiom( neq, Reason::idt_collapse );
      Debug("datatypes") << "Collapse selector " << neq << endl;
      addEquality( neq );
    } else {
      //see whether we can prove that the selector is applied to the wrong tester
      Node tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), tmp );
      Node conflict;
      unsigned r;
      checkTester( tester, conflict, r );
      if( !conflict.isNull() ) {
        Debug("datatypes") << "Applied selector " << t << " to provably wrong constructor." << endl;
        // conflict = c ^ tester, conflict => false
        // want to say c => ~tester
        //must remove tester from conflict
        if( conflict.getKind()==kind::AND ){
          NodeBuilder<> jt(kind::AND);
          for( int i=0; i<(int)conflict.getNumChildren(); i++ ){
            if( conflict[i]!=tester ){
              jt << conflict[i];
            }
          }
          conflict = ( jt.getNumChildren()==1 ) ? jt.getChild( 0 ) : jt;
        }else if( conflict==tester ){
          conflict = Node::null();
        }
        if( conflict!=tester.notNode() ){
          d_em.addNode( tester.notNode(), conflict, r );
        }

        if( tmp != t[0] ) {
          Node teq = NodeManager::currentNM()->mkNode( EQUAL, tmp, t[0] );
          d_em.addNode( teq, &d_cce );
          Node exp = NodeManager::currentNM()->mkNode( AND, tester.notNode(), teq );
          tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), t[0] );
          d_em.addNode( tester.notNode(), exp, Reason::idt_tcong );
        }
        retNode = selType[1].mkGroundTerm();
        Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );

        d_em.addNode( neq, tester.notNode(), Reason::idt_collapse2 );
        addEquality( neq );
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
        //Debug("datatypes") << "Merge selector " << s << " into " << b
        //Debug("datatypes") << ", find is " << find( s[0] ) << endl;
        Assert( s.getKind() == APPLY_SELECTOR && find( s[0] ) == b );
        if( b != s[0] ) {
          Node t = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, s.getOperator(), b );
          d_cc.addTerm( t );
          collectTerms( t );
        }
        s = collapseSelector( s );
        if( hasConflict() ) {
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
        //if there is only one constructor, then it must be
        const Datatype& dt = ((DatatypeType)(t.getType()).toType()).getDatatype();
        if( dt.getNumConstructors()==1 ){
          Node tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[0].getTester() ), t );
          addTester( tester );
          d_em.addNodeAxiom( tester, Reason::idt_texhaust );
        }
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
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      Debug("datatypes-cycles") << "Subterm " << n << " -> " << n[i] << endl;
      bool result CVC4_UNUSED = d_cycle_check.addEdgeNode( n, n[i] );
      Assert( !result );    //this should not create any new cycles (relevant terms should have been recorded before)
    }
  }else{
    if( n.getKind() == APPLY_SELECTOR ) {
      if( d_selectors.find( n ) == d_selectors.end() ) {
        Debug("datatypes") << "  Found selector " << n << endl;
        d_selectors[ n ] = true;
        d_cc.addTerm( n );
        Node tmp = find( n[0] );
        checkInstantiate( tmp );

        Node s = n;
        if( tmp != n[0] ) {
          s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, n.getOperator(), tmp );
        }
        s = collapseSelector( s );
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

#define DELAY_MERGE

void TheoryDatatypes::addEquality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  if( find( eq[0] ) != find( eq[1] ) ) {
    Debug("datatypes") << "Add equality " << eq << "." << endl;
    Debug("datatypes-debug-pf") << "Add equality " << eq << "." << endl;

    //setup merge pending list
#ifdef DELAY_MERGE
    d_merge_pending.push_back( vector< pair< Node, Node > >() );
    bool prevNoMerge = d_noMerge;
    d_noMerge = true;
#endif

    d_cc.addTerm(eq[0]);
    d_cc.addTerm(eq[1]);
    d_cce.assert(eq);
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-cycles") ){
      d_currEqualities.push_back(eq);
    }

#ifdef DELAY_MERGE
    //record which nodes are waiting to be merged
    d_noMerge = prevNoMerge;
    vector< pair< Node, Node > > mp;
    mp.insert( mp.begin(), 
               d_merge_pending[d_merge_pending.size()-1].begin(), 
               d_merge_pending[d_merge_pending.size()-1].end() );
    d_merge_pending.pop_back();
#endif

    //merge original nodes
    if( !hasConflict() ) {
      merge( eq[0], eq[1] );
    }
#ifdef DELAY_MERGE
    //merge nodes waiting to be merged
    for( int i=0; i<(int)mp.size(); i++ ) {
      if( !hasConflict() ) {
        merge( mp[i].first, mp[i].second );
      }
    }
#endif
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

void TheoryDatatypes::checkCycles() {
  for( BoolMap::iterator i = d_reps.begin(); i != d_reps.end(); i++ ) {
    if( (*i).second ) {
      map< Node, bool > visited;
      NodeBuilder<> explanation(kind::AND);
      if( searchForCycle( (*i).first, (*i).first, visited, explanation ) ) {
        Node cCycle = explanation.getNumChildren() == 1 ? explanation.getChild( 0 ) : explanation;
        d_em.addNodeConflict( cCycle, Reason::idt_cycle );
        Debug("datatypes") << "Detected cycle for " << (*i).first << endl;
        Debug("datatypes") << "Conflict is " << cCycle << endl;
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
          if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n, n[i] ) ){
            Debug("datatypes-cycles") << "Cycle subterm: " << n << " is not -> " << n[i] << "!!!!" << std::endl;
          }
          if( nn != n[i] ) {
            if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n[i], nn ) ){
              Debug("datatypes-cycles") << "Cycle equality: " << n[i] << " is not -> " << nn << "!!!!" << std::endl;
            }
            Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, nn, n[i] );
            d_em.addNode( ccEq, &d_cce );
            explanation << ccEq;
          }
          return true;
        }
      }
    }
  }
  return false;
}
