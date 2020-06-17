/*********************                                                        */
/*! \file sygus_invariance.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus invariance tests
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_INVARIANCE_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_INVARIANCE_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDbSygus;
class SynthConjecture;

/* SygusInvarianceTest
*
* This class is the standard interface for term generalization
* in SyGuS. Its interface is a single function is_variant,
* which is a virtual condition for SyGuS terms.
*
* The common use case of invariance tests is when constructing
* minimal explanations for refinement lemmas in the
* counterexample-guided inductive synthesis (CEGIS) loop.
* See sygus_explain.h for more details.
*/
class SygusInvarianceTest
{
 public:
  virtual ~SygusInvarianceTest() {}

  /** Is nvn invariant with respect to this test ?
   *
   * - nvn is the term to check whether it is invariant.
   * - x is a variable such that the previous call to
   *   is_invariant (if any) was with term nvn_prev, and
   *   nvn is equal to nvn_prev with some subterm
   *   position replaced by x. This is typically used
   *   for debugging only.
   */
  bool is_invariant(TermDbSygus* tds, Node nvn, Node x)
  {
    if (invariant(tds, nvn, x))
    {
      d_update_nvn = nvn;
      return true;
    }
    return false;
  }
  /** get updated term */
  Node getUpdatedTerm() { return d_update_nvn; }
  /** set updated term */
  void setUpdatedTerm(Node n) { d_update_nvn = n; }
 protected:
  /** result of the node that satisfies this invariant */
  Node d_update_nvn;
  /** check whether nvn[ x ] is invariant */
  virtual bool invariant(TermDbSygus* tds, Node nvn, Node x) = 0;
};

/** EquivSygusInvarianceTest
*
* This class tests whether a term evaluates via evaluation
* operators in the deep embedding (Section 4 of Reynolds
* et al. CAV 2015) to fixed term d_result.
*
* For example, consider a SyGuS evaluation function eval
* for a synthesis conjecture with arguments x and y.
* Notice that the term t = (mult x y) is such that:
*   eval( t, 0, 1 ) ----> 0
* This test is invariant on the content of the second
* argument of t, noting that:
*   eval( (mult x _), 0, 1 ) ----> 0
* as well, via a call to EvalSygusInvarianceTest::invariant.
*
* Another example, t = ite( gt( x, y ), x, y ) is such that:
*   eval( t, 2, 3 ) ----> 3
* This test is invariant on the second child of t, noting:
*   eval( ite( gt( x, y ), _, y ), 2, 3 ) ----> 3
*/
class EvalSygusInvarianceTest : public SygusInvarianceTest
{
 public:
  EvalSygusInvarianceTest()
      : d_kind(kind::UNDEFINED_KIND), d_is_conjunctive(false)
  {
  }

  /** initialize this invariance test
   *
   * This sets d_terms/d_var/d_result, where we are checking whether:
   *   <d_kind>(d_terms) { d_var -> n } ----> d_result.
   * for terms n.
   */
  void init(Node conj, Node var, Node res);

  /** do evaluate with unfolding, using the cache of this class */
  Node doEvaluateWithUnfolding(TermDbSygus* tds, Node n);

 protected:
  /** does d_terms{ d_var -> nvn } still rewrite to d_result? */
  bool invariant(TermDbSygus* tds, Node nvn, Node x) override;

 private:
  /** the formulas we are evaluating */
  std::vector<Node> d_terms;
  /** the variable */
  TNode d_var;
  /** the result of the evaluation */
  Node d_result;
  /** the parent kind we are checking, undefined if size(d_terms) is 1. */
  Kind d_kind;
  /** whether we are conjunctive
   *
   * If this flag is true, then the evaluation tests:
   *   d_terms[1] {d_var -> n} = d_result ... d_term[k] {d_var -> n} = d_result
   * should be processed conjunctively, that is,
   * <d_kind>(d_terms) { d_var -> n } = d_result only if each of the above
   * holds. If this flag is false, then these tests are interpreted
   * disjunctively, i.e. if one child test succeeds, the overall test succeeds.
   */
  bool d_is_conjunctive;
  /** cache of n -> the simplified form of eval( n ) */
  std::unordered_map<Node, Node, NodeHashFunction> d_visited;
};

/** EquivSygusInvarianceTest
*
* This class tests whether a builtin version of a
* sygus term is equivalent up to rewriting to a RHS value bvr.
*
* For example,
*
* ite( t>0, 0, 0 ) + s*0 ----> 0
*
* This test is invariant on the condition t>0 and s, since:
*
* ite( _, 0, 0 ) + _*0 ----> 0
*
* for any values of _.
*
* It also manages the case where the rewriting is invariant
* wrt a finite set of examples occurring in the conjecture.
* (EX1) : For example if our input examples are:
* (x,y,z) = (3,2,4), (5,2,6), (3,2,1)
* On these examples, we have:
*
* ite( x>y, z, 0) ---> 4,6,1
*
* which is invariant on the second argument:
*
* ite( x>y, z, _) ---> 4,6,1
*
* For details, see Reynolds et al SYNT 2017.
*/
class EquivSygusInvarianceTest : public SygusInvarianceTest
{
 public:
  EquivSygusInvarianceTest() : d_conj(nullptr) {}

  /** initialize this invariance test
   * tn is the sygus type for e
   * aconj/e are used for conjecture-specific symmetry breaking
   * bvr is the builtin version of the right hand side of the rewrite that we
   * are checking for invariance
   */
  void init(
      TermDbSygus* tds, TypeNode tn, SynthConjecture* aconj, Node e, Node bvr);

 protected:
  /** checks whether the analog of nvn still rewrites to d_bvr */
  bool invariant(TermDbSygus* tds, Node nvn, Node x) override;

 private:
  /** the conjecture associated with the enumerator d_enum */
  SynthConjecture* d_conj;
  /** the enumerator associated with the term for which this test is for */
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
 * This class tests whether a sygus term involves
 * division by zero.
 *
 * For example the test for:
 *    ( x + ( y/0 )*2 )
 * is invariant on the contents of _ below:
 *    ( _ + ( _/0 )*_ )
 */
class DivByZeroSygusInvarianceTest : public SygusInvarianceTest
{
 public:
  DivByZeroSygusInvarianceTest() {}

 protected:
  /** checks whether nvn involves division by zero. */
  bool invariant(TermDbSygus* tds, Node nvn, Node x) override;
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
* Then, this class is used when there is a candidate solution t[x1]
* such that either:
*   contains( "abc abc", t["abc"] ) ---> false or
*   contains( "de de", t["de"] ) ---> false
*
* It is used to determine whether certain generalizations of t[x1]
* are still sufficient to falsify one of the above containments.
*
* For example:
*
* The test for str.++( x1, "d" ) is invariant on its first argument
*   ...since contains( "abc abc", str.++( _, "d" ) ) ---> false
* The test for str.replace( "de", x1, "b" ) is invariant on its third argument
*   ...since contains( "abc abc", str.replace( "de", "abc", _ ) ) ---> false
*/
class NegContainsSygusInvarianceTest : public SygusInvarianceTest
{
 public:
  NegContainsSygusInvarianceTest() : d_isUniversal(false) {}

  /** initialize this invariance test
   *  e is the enumerator which we are reasoning about (associated with a synth
   *    fun).
   *  ex is the list of inputs,
   *  exo is the list of outputs,
   *  ncind is the set of possible example indices to check invariance of
   *  non-containment.
   *    For example, in the above example, when t[x1] = "ab", then this
   *    has the index 1 since contains("de de", "ab") ---> false but not
   *    the index 0 since contains("abc abc","ab") ---> true.
   */
  void init(Node e,
            std::vector<std::vector<Node> >& ex,
            std::vector<Node>& exo,
            std::vector<unsigned>& ncind);
  /** set universal
   *
   * This updates the semantics of this check such that *all* instead of some
   * examples must fail the containment test.
   */
  void setUniversal() { d_isUniversal = true; }

 protected:
  /**
   * Checks if contains( out_i, nvn[in_i] ) --> false for some I/O pair i; if
   * d_isUniversal is true, then we check if the rewrite holds for *all* I/O
   * pairs.
   */
  bool invariant(TermDbSygus* tds, Node nvn, Node x) override;

 private:
  /** The enumerator whose value we are considering in this invariance test */
  Node d_enum;
  /** The input examples */
  std::vector<std::vector<Node> > d_ex;
  /** The output examples for the enumerator */
  std::vector<Node> d_exo;
  /** The set of I/O pair indices i such that
   *    contains( out_i, nvn[in_i] ) ---> false
   */
  std::vector<unsigned> d_neg_con_indices;
  /** requires not being in all examples */
  bool d_isUniversal;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_INVARIANCE_H */
