/*********************                                                        */
/*! \file sygus_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus invariance tests
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_INVARIANCE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_INVARIANCE_H

#include <vector>
#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDbSygus;
class CegConjecture;

// TODO
/* SygusInvarianceTest
* 
* This class is the standard interface for term generalization
* in SyGuS. Its interface is a single function is_variant,
* 
* 
* The common use case of invariance tests is when constructing
* minimal explanations for refinement lemmas in the
* counterexample-guided inductive synthesis (CEGIS) loop.
* For sygus_explain.h for more details.
* 
*/
class SygusInvarianceTest {
public:
  bool is_invariant( TermDbSygus * tds, Node nvn, Node x ){
    if( invariant( tds, nvn, x ) ){
      d_update_nvn = nvn;
      return true;
    }else{
      return false;
    }
  }
  /** get updated term */
  Node getUpdatedTerm() { return d_update_nvn; }
  /** get updated term */
  void setUpdatedTerm( Node n ) { 
    d_update_nvn = n; 
  }
protected:
  /** result of the node after invariant replacements */
  Node d_update_nvn;
  /** check whether nvn[ x ] is invariant */
  virtual bool invariant( TermDbSygus * tds, Node nvn, Node x ) = 0;
};

/** EquivSygusInvarianceTest
*
* This class is used to construct a minimal shape of a term that 
* evaluates via evaluation operators in the deep embedding 
* (Section 4 of Reynolds et al. CAV 2015) to fixed term d_result.
* 
* For example, consider a SyGuS evaluation function eval
* for a synthesis conjecture with arguments x and y. Say we 
* wish to generalize the term t = (mult x y) such that:
* 
*   eval( t, 0, 1 ) ----> 0
* 
* This can be minimized to t = (mul x _), noting that:
* 
*   eval( (mult x _), 0, 1 ) ----> 0
* 
* Another example, t
* 
*   eval( t, 0, 1 ) ----> 0
* 
*/
class EvalSygusInvarianceTest : public SygusInvarianceTest {
public:
  EvalSygusInvarianceTest(){}
  ~EvalSygusInvarianceTest(){}
  Node d_conj;
  TNode d_var;
  std::unordered_map< Node, Node, NodeHashFunction > d_visited;
  Node d_result;
protected:
  bool invariant( TermDbSygus * tds, Node nvn, Node x );
};


/** EquivSygusInvarianceTest
*
* This class is used to construct a minimal shape of a term that is equivalent
* up to rewriting to a RHS value bvr.
*
* For example,
*
* ite( t>0, 0, 0 ) + s*0 ----> 0
*
* can be minimized to:
*
* ite( _, 0, 0 ) + _*0 ----> 0
*
* It also manages the case where the rewriting is invariant wrt a finite set of
* examples occurring in the conjecture.  
* (EX1) : For example if our input examples are:
* (x,y,z) = (3,2,4), (5,2,6), (3,2,1)
* On these examples, we have:
*
* ite( x>y, z, 0) ---> 4,6,1
*
* which can be minimized to:
*
* ite( x>y, z, _) ---> 4,6,1
*
* For details, see Reynolds et al SYNT 2017.
*/
class EquivSygusInvarianceTest : public SygusInvarianceTest {
 public:
  EquivSygusInvarianceTest() : d_conj(nullptr) {}
  ~EquivSygusInvarianceTest() {}
  /** initialize this invariance test
    * tn is the sygus type for e
    * aconj/e are used for conjecture-specific symmetry breaking
    * bvr is the builtin version of the right hand side of the rewrite that we are
    * checking for invariance
    */
  void init(TermDbSygus* tds, TypeNode tn,
            CegConjecture* aconj, Node e, Node bvr);
 protected:
  /** does nvn still rewrite to d_bvr? */
  bool invariant(TermDbSygus* tds, Node nvn, Node x);
 private:
  /** the conjecture associated with the enumerator d_enum */
  CegConjecture* d_conj;
  /** the enumerator associated with the term we are doing an invariance test
   * for */
  Node d_enum;
  /** the RHS of the evaluation */
  Node d_bvr;
  /** the result of the examples 
   * In (EX1), this is (4,6,1)
   */
  std::vector<Node> d_exo;
};

/** DivByZeroSygusInvarianceTest 
 * 
 * This class is used to construct a minimal shape of a term that involves
 * division by zero.
 * 
 * For example:
 *    ( x + ( y/0 )*2 )
 * can be generalized to:
 *    ( _ + ( _/0 )*_ )
 */
class DivByZeroSygusInvarianceTest : public SygusInvarianceTest {
public:
  DivByZeroSygusInvarianceTest(){}
  ~DivByZeroSygusInvarianceTest(){}

protected:
  bool invariant( TermDbSygus * tds, Node nvn, Node x );
};

/** NegContainsSygusInvarianceTest
*
* This class is used to construct a minimal shape of a term that cannot
* be contained in at least one output of an I/O pair.
*
* Say our PBE conjecture is:
*
* exists f.
*   f( "abc" ) = "abc abc" ^
*   f( "de" ) = "de de"
*
* Then, this class is used when there is a candidate solution t[x1] such that
* either
*   contains( "abc abc", t["abc"] ) ---> false or
*   contains( "de de", t["de"] ) ---> false
*
* In particular it is used to determine whether certain generalizations of t[x1]
* are still sufficient to falsify one of the above containments.
*
* For example:
*
* str.++( x1, "d" ) can be minimized to str.++( _, "d" )
*   ...since contains( "abc abc", str.++( y, "d" ) ) ---> false,
*      for any y.
* str.replace( "de", x1, "b" ) can be minimized to str.replace( "de", x1, _ )
*   ...since contains( "abc abc", str.replace( "de", "abc", y ) ) ---> false,
*      for any y.
*/
class NegContainsSygusInvarianceTest : public SygusInvarianceTest {
public:
  NegContainsSygusInvarianceTest() : d_conj(nullptr){}
  ~NegContainsSygusInvarianceTest(){}

  /** initialize this invariance test
  *  cpbe is the conjecture utility.
  *  e is the enumerator which we are reasoning about (associated with a synth
  *    fun).
  *  exo is the list of outputs of the PBE conjecture.
  *  ncind is the set of possible indices of the PBE conjecture to check
  *    invariance of non-containment.
  *    For example, in the above example, when t[x1] = "ab", then this
  *    has the index 1 since contains("de de", "ab") ---> false but not
  *    the index 0 since contains("abc abc","ab") ---> true.
  */
  void init(CegConjecture* conj,
            Node e,
            std::vector<Node>& exo,
            std::vector<unsigned>& ncind);

 protected:
  /** checks if contains( out_i, nvn[in_i] ) --> false for some I/O pair i. */
  bool invariant( TermDbSygus * tds, Node nvn, Node x );

 private:
  /** The enumerator whose value we are considering in this invariance test */
  Node d_enum;
  /** The output examples for the enumerator */
  std::vector<Node> d_exo;
  /** The set of I/O pair indices i such that
   *    contains( out_i, nvn[in_i] ) ---> false
   */
  std::vector<unsigned> d_neg_con_indices;
  /** reference to the conjecture associated with this test */
  CegConjecture* d_conj;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_INVARIANCE_H */
