/*********************                                                        */
/*! \file theory_arrays.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of arrays
 **
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"
#include "theory/arrays/union_find.h"
#include "util/congruence_closure.h"
#include "array_info.h"
#include "util/hash.h"
#include "util/ntuple.h"
#include "util/stats.h"
#include "util/backtrackable.h"
#include "theory/arrays/static_fact_manager.h"

#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {
namespace arrays {

/**
 * Decision procedure for arrays.
 *
 * Overview of decision procedure:
 *
 * Preliminary notation:
 *   Stores(a)  = {t | a ~ t and t = store( _ _ _ )} 
 *   InStores(a) = {t | t = store (b _ _) and a ~ b }
 *   Indices(a) = {i | there exists a term b[i] such that a ~ b or store(b i v)}
 *   ~ represents the equivalence relation based on the asserted equalities in the
 *   current context.
 * 
 * The rules implemented are the following:
 *             store(b i v)
 *     Row1 -------------------
 *          store(b i v)[i] = v
 * 
 *           store(b i v)  a'[j]
 *     Row ---------------------- [ a' ~ store(b i v) or a' ~ b ]
 *           i = j OR a[j] = b[j]
 * 
 *          a  b same kind arrays
 *     Ext ------------------------ [ a!= b in current context, k new var]
 *           a = b OR a[k] != b[k]p
 * 
 * 
 *  The Row1 one rule is implemented implicitly as follows:
 *     - for each store(b i v) term add the following equality to the congruence
 *       closure store(b i v)[i] = v
 *     - if one of the literals in a conflict is of the form store(b i v)[i] = v
 *       remove it from the conflict
 * 
 *  Because new store terms are not created, we need to check if we need to
 *  instantiate a new Row axiom in the following cases:
 *     1. the congruence relation changes (i.e. two terms get merged)
 *         - when a new equality between array terms a = b is asserted we check if
 *           we can instantiate a Row lemma for all pairs of indices i where a is
 *           being read and stores
 *         - this is only done during full effort check
 *     2. a new read term is created either as a consequences of an Ext lemma or a
 *        Row lemma
 *         - this is implemented in the checkRowForIndex method which is called
 *           when preregistering a term of the form a[i].
 *         - as a consequence lemmas are instantiated even before full effort check
 * 
 *  The Ext axiom is instantiated when a disequality is asserted during full effort
 *  check. Ext lemmas are stored in a cache to prevent instantiating essentially
 *  the same lemma multiple times.
 */
class TheoryArrays : public Theory {

private:


  class CongruenceChannel {
    TheoryArrays* d_arrays;

  public:
    CongruenceChannel(TheoryArrays* arrays) : d_arrays(arrays) {}
    void notifyCongruent(TNode a, TNode b) {
      d_arrays->notifyCongruent(a, b);
    }
  }; /* class CongruenceChannel*/
  friend class CongruenceChannel;

  /**
   * Output channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel, CONGRUENCE_OPERATORS_1
                                 (kind::SELECT)> d_cc;

  /**
   * (Temporary) fact manager for preprocessing - eventually handle this with
   * something more standard (like congruence closure module)
   */
  StaticFactManager d_staticFactManager;

  /**
   * Cache for proprocessing of atoms.
   */
  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_ppCache;

  /**
   * Union find for storing the equalities.
   */

  UnionFind<Node, NodeHashFunction> d_unionFind;

  Backtracker<TNode> d_backtracker;


  /**
   * Context dependent map from a congruence class canonical representative of
   * type array to an Info pointer that keeps track of information useful to axiom
   * instantiation
   */

  ArrayInfo d_infoMap;

  /**
   * Received a notification from the congruence closure algorithm that the two
   * nodes a and b have become congruent.
   */

  void notifyCongruent(TNode a, TNode b);


  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > CTNodeListAlloc;
  typedef context::CDMap<Node, CTNodeListAlloc*, NodeHashFunction> CNodeTNodesMap;
  typedef context::CDMap<TNode, List<TNode>*, TNodeHashFunction > EqLists;


  typedef __gnu_cxx::hash_map<TNode, CTNodeList*, TNodeHashFunction> NodeTNodesMap;
  /**
   * List of all disequalities this theory has seen. Maintains the invariant that
   * if a is in the disequality list of b, then b is in that of a. FIXME? make non context dep map
   * */
  CNodeTNodesMap d_disequalities;
  EqLists d_equalities;
  context::CDList<TNode> d_prop_queue;

  void checkPropagations(TNode a, TNode b);

  /** List of all atoms the SAT solver knows about and are candidates for
   *  propagation. */
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> d_atoms;

  /** List of disequalities needed to construct explanations for propagated
   * row lemmas */

  context::CDMap<TNode, std::pair<TNode, TNode>, TNodeHashFunction> d_explanations;

  /**
   * stores the conflicting disequality (still need to call construct
   * conflict to get the actual explanation)
   */
  Node d_conflict;

  typedef context::CDList< quad<TNode, TNode, TNode, TNode > > QuadCDList;


  /**
   * Ext lemma workslist that stores extensionality lemmas that still need to be added
   */
  std::hash_set<std::pair<TNode, TNode>, TNodePairHashFunction> d_extQueue;

  /**
   * Row Lemma worklist, stores lemmas that can still be added to the SAT solver
   * to be emptied during full effort check
   */
  std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction > d_RowQueue;

  /**
   * Extensionality lemma cache which stores the array pair (a,b) for which
   * a lemma of the form (a = b OR a[k]!= b[k]) has been added to the SAT solver.
   */
  std::hash_set<std::pair<TNode, TNode>, TNodePairHashFunction> d_extAlreadyAdded;

  /**
   * Read-over-write lemma cache storing a quadruple (a,b,i,j) for which a
   * the lemma (i = j OR a[j] = b[j]) has been added to the SAT solver. Needed
   * to prevent infinite recursion in addRowLemma.
   */
  std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction > d_RowAlreadyAdded;

  /*
   * Congruence helper methods
   */

  void addDiseq(TNode diseq);
  void addEq(TNode eq);

  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode a, TNode b);
  Node constructConflict(TNode diseq);

  /**
   * Merges two congruence classes in the internal union-find and checks for a
   * conflict.
   */

  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;

  inline void setCanon(TNode a, TNode b);

  void queueRowLemma(TNode a, TNode b, TNode i, TNode j);
  inline void queueExtLemma(TNode a, TNode b);

  /**
   * Adds a Row lemma of the form:
   *    i = j OR a[j] = b[j]
   */
  void addRowLemma(TNode a, TNode b, TNode i, TNode j);

  /**
   * Adds a new Ext lemma of the form
   *    a = b OR a[k]!=b[k], for a new variable k
   */
  void addExtLemma(TNode a, TNode b);

  /**
   * Because Row1 axioms of the form (store a i v) [i] = v are not added as
   * explicitly but are kept track of internally, is axiom recognizez an axiom
   * of the above form given the two terms in the equality.
   */
  bool isAxiom(TNode lhs, TNode rhs);


  bool isRedundandRowLemma(TNode a, TNode b, TNode i, TNode j);
  bool isRedundantInContext(TNode a, TNode b, TNode i, TNode j);



  bool alreadyAddedRow(TNode a, TNode b, TNode i, TNode j) {
    //Trace("arrays-lem")<<"alreadyAddedRow check for "<<a<<" "<<b<<" "<<i<<" "<<j<<"\n";
    std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction >::const_iterator it = d_RowAlreadyAdded.begin();
    a = find(a);
    b = find(b);
    i = find(i);
    j = find(j);

    for( ; it!= d_RowAlreadyAdded.end(); it++) {

      TNode a_ = find((*it).first);
      TNode b_ = find((*it).second);
      TNode i_ = find((*it).third);
      TNode j_ = find((*it).fourth);
      if( a == a_ && b == b_ && i==i_ && j==j_) {
        //Trace("arrays-lem")<<"alreadyAddedRow found "<<a_<<" "<<b_<<" "<<i_<<" "<<j_<<"\n";
        return true;
      }
    }
    return false;
  }


  bool isNonLinear(TNode n);

  /**
   * Checks if any new Row lemmas need to be generated after merging arrays a
   * and b; called after setCanon.
   */
  void checkRowLemmas(TNode a, TNode b);

  /**
   * Called after a new select term a[i] is created to check whether new Row
   * lemmas need to be instantiated.
   */
  void checkRowForIndex(TNode i, TNode a);

  void checkStore(TNode a);
  /**
   * Lemma helper functions to prevent changing the list we are iterating through.
   */

  void insertInQuadQueue(std::set<quad<TNode, TNode, TNode, TNode> >& queue, TNode a, TNode b, TNode i, TNode j){
    if(i != j) {
      queue.insert(make_quad(a,b,i,j));
    }
  }

  void dischargeLemmas() {
    // we need to swap the temporary lists because adding a lemma calls preregister
    // which might modify the d_RowQueue we would be iterating through
    std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction > temp_Row;
    temp_Row.swap(d_RowQueue);

    std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction >::const_iterator it1 = temp_Row.begin();
    for( ; it1!= temp_Row.end(); it1++) {
      if(!isRedundantInContext((*it1).first, (*it1).second, (*it1).third, (*it1).fourth)) {
        addRowLemma((*it1).first, (*it1).second, (*it1).third, (*it1).fourth);
      }
      else {
        // add it to queue may be needed later
        queueRowLemma((*it1).first, (*it1).second, (*it1).third, (*it1).fourth);
      }
    }

    std::hash_set<std::pair<TNode, TNode>, TNodePairHashFunction>  temp_ext;
    temp_ext.swap(d_extQueue);

    std::hash_set<std::pair<TNode, TNode>, TNodePairHashFunction> ::const_iterator it2 = temp_ext.begin();
    for(; it2 != temp_ext.end(); it2++) {
      addExtLemma((*it2).first, (*it2).second);
    }
  }

  /** Checks if instead of adding a lemma of the form i = j OR  a[j] = b[j]
   * we can propagate either i = j or NOT a[j] = b[j] and does the propagation.
   * Returns whether it did propagate.
   */
  bool propagateFromRow(TNode a, TNode b, TNode i, TNode j);

  TNode areDisequal(TNode a, TNode b);



  /*
   * === STATISTICS ===
   */

  /** number of Row lemmas */
  IntStat d_numRow;
  /** number of Ext lemmas */
  IntStat d_numExt;

  /** number of propagations */
  IntStat d_numProp;
  IntStat d_numExplain;
  /** time spent in check() */
  TimerStat d_checkTimer;

  bool d_donePreregister;

  Node preprocessTerm(TNode term);
  Node recursivePreprocessTerm(TNode term);

public:
  TheoryArrays(context::Context* c, OutputChannel& out, Valuation valuation);
  ~TheoryArrays();

  /**
   * Stores in d_infoMap the following information for each term a of type array:
   *
   *    - all i, such that there exists a term a[i] or a = store(b i v)
   *      (i.e. all indices it is being read atl; store(b i v) is implicitly read at
   *      position i due to the implicit axiom store(b i v)[i] = v )
   *
   *    - all the stores a is congruent to (this information is context dependent)
   *
   *    - all store terms of the form store (a i v) (i.e. in which a appears
   *      directly; this is invariant because no new store terms are created)
   *
   * Note: completeness depends on having pre-register called on all the input
   *       terms before starting to instantiate lemmas.
   */
  void preRegisterTerm(TNode n) {
    //TimerStat::CodeTimer codeTimer(d_preregisterTimer);
    Trace("arrays-preregister")<<"Arrays::preRegisterTerm "<<n<<"\n";
    //TODO: check non-linear arrays with an AlwaysAssert!!!
    //if(n.getType().isArray())

    switch(n.getKind()) {
    case kind::EQUAL:
      // stores the seen atoms for propagation
      Trace("arrays-preregister")<<"atom "<<n<<"\n";
      d_atoms.insert(n);
      // add to proper equality lists
      addEq(n);
      break;
    case kind::SELECT:
      //Trace("arrays-preregister")<<"at level "<<getContext()->getLevel()<<"\n";
      d_infoMap.addIndex(n[0], n[1]);
      checkRowForIndex(n[1], find(n[0]));
      //Trace("arrays-preregister")<<"n[0] \n";
      //d_infoMap.getInfo(n[0])->print();
      //Trace("arrays-preregister")<<"find(n[0]) \n";
      //d_infoMap.getInfo(find(n[0]))->print();
      break;

    case kind::STORE:
    {
      // this should always be called at level0 since we do not create new store terms
      TNode a = n[0];
      TNode i = n[1];
      TNode v = n[2];

      NodeManager* nm = NodeManager::currentNM();
      Node ni = nm->mkNode(kind::SELECT, n, i);
      Node eq = nm->mkNode(kind::EQUAL, ni, v);

      d_cc.addEquality(eq);

      d_infoMap.addIndex(n, i);
      d_infoMap.addStore(n, n);
      d_infoMap.addInStore(a, n);

      checkStore(n);

      break;
    }
    default:
      Trace("darrays")<<"Arrays::preRegisterTerm non-array term. \n";
    }
  }

  //void registerTerm(TNode n) {
  //  Trace("arrays-register")<<"Arrays::registerTerm "<<n<<"\n";
  //}

  void presolve() {
    Trace("arrays")<<"Presolving \n";
    d_donePreregister = true;
  }

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);

  void propagate(Effort e) {

    Trace("arrays-prop")<<"Propagating \n";

    context::CDList<TNode>::const_iterator it = d_prop_queue.begin();
    /*
    for(; it!= d_prop_queue.end(); it++) {
      TNode eq = *it;
      if(d_valuation.getSatValue(eq).isNull()) {
        //FIXME remove already propagated literals?
        d_out->propagate(eq);
        ++d_numProp;
      }
    }*/
    //d_prop_queue.deleteSelf();
    /*
    __gnu_cxx::hash_set<TNode, TNodeHashFunction>::const_iterator it = d_atoms.begin();

    for(; it!= d_atoms.end(); it++) {
      TNode eq = *it;
      Assert(eq.getKind()==kind::EQUAL);
      Trace("arrays-prop")<<"value of "<<eq<<" ";
      Trace("arrays-prop")<<d_valuation.getSatValue(eq);
      if(find(eq[0]) == find(eq[1])) {
        Trace("arrays-prop")<<" eq \n";
        ++d_numProp;
      }
    }
    */

  }
  void explain(TNode n);

  Node getValue(TNode n);
  SolveStatus solve(TNode in, SubstitutionMap& outSubstitutions);
  Node preprocess(TNode atom);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryArrays"); }

};/* class TheoryArrays */

inline void TheoryArrays::setCanon(TNode a, TNode b) {
  d_unionFind.setCanon(a, b);
}

inline TNode TheoryArrays::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryArrays::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */
