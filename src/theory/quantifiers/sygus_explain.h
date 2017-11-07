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
 ** \brief sygus explanations
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_EXPLAIN_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_EXPLAIN_H

#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/sygus_invariance.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Recursive term builder
 *
 * This is a utility used to generate variants
 * of a term n, where subterms of n can be replaced
 * by others via calls to replaceChild(...).
 *
 * This class maintains a "context", which indicates
 * a position in term n. Below, we call the subterm of
 * the initial term n at this position the "active term".
 *
 */
class TermRecBuild
{
 public:
  TermRecBuild() {}
  /** set the initial term to n
   *
   * The context initially empty, that is,
   * the active term is initially n.
   */
  void init(Node n);
  /** push the context
   *
   * This updates the context so that the
   * active term is updated to curr[p], where
   * curr is the previously active term.
   */
  void push(unsigned p);
  /** pop the context */
  void pop();
  /** indicates that the i^th child of the active
   * term should be replaced by r in calls to build().
   */
  void replaceChild(unsigned i, Node r);
  /** get the i^th child of the active term */
  Node getChild(unsigned i);
  /** build the (modified) version of the term
   * we intialized via the call to init().
   */
  Node build(unsigned p = 0);

 private:
  /** stack of active terms */
  std::vector<Node> d_term;
  /** stack of children of active terms
   * Notice that these may be modified with calls to replaceChild(...).
   */
  std::vector<std::vector<Node> > d_children;
  /** stack the kind of active terms */
  std::vector<Kind> d_kind;
  /** stack of whether the active terms had an operator */
  std::vector<bool> d_has_op;
  /** stack of positions that were pushed via calls to push(...) */
  std::vector<unsigned> d_pos;
  /** add term to the context stack */
  void addTerm(Node n);
};

/*The SygusExplain utility
 * 
 * This class is used to produce explanations for refinement lemmas
 * in the counterexample-guided inductive synthesis (CEGIS) loop. 
 *
 * When given an invariance test T traverses the AST of a given term, 
 * uses TermRecBuild to replace various subterms by fresh variables and
 * recheck whether the invariant, as specified by T still holds.
 * If it does, then we may exclude the explanation for that that subterm.
 * 
 * For example, 
 * 
 */
class SygusExplain
{
public:
  SygusExplain( TermDbSygus * tdb ) : d_tdb(tdb){}
  ~SygusExplain(){}
  /** get explanation for constant equality
   * 
   * This function constructs an explanation, stored in exp, such that:
   * - All formulas in exp are of the form ((_ is C) ns), where ns
   *   is a chain of selectors applied to n, and
   * - exp => ( n = vn )
   */
  void getExplanationForConstantEquality( Node n, Node vn, std::vector< Node >& exp );
  /** returns the conjunction of exp computed in the above function */
  Node getExplanationForConstantEquality( Node n, Node vn );
  /** get explanation for constant equality
   * This is identical to the above function except that we 
   * take an additional argument cexc, which says which
   * children of vn should be excluded from the explanation.
   * 
   * For example, if vn = plus( x, y ) and cexc is { 0 -> true },
   * then we appended to exp :
   *   { ((_ is plus) n), ((_ is y) n.1) }
   */
  void getExplanationForConstantEquality( Node n, Node vn, std::vector< Node >& exp, std::map< unsigned, bool >& cexc );
  /** returns the conjunction of exp computed in the above function */
  Node getExplanationForConstantEquality( Node n, Node vn, std::map< unsigned, bool >& cexc );
  // we have n = vn => eval( n ) = bvr, returns exp => eval( n ) = bvr
  //   ensures the explanation still allows for vnr
  /** get explanation for 
   * 
   * As a precondition, we have that:
   *   n = vn => eval( n ) = bvr 
   *   sz is the term size of vn
   * where eval is the sygus evaluation function for n's type 
   * (see Section 4 of Reynolds et al. CAV 2015).
   * 
   * This function constructs an explanation, stored in exp, such that:
   * - All formulas in exp are of the form ((_ is C) n),
   * - exp => eval( n ) = vn
   * - (if applicable) exp => ( n != vnr )
   * - 
   * 
   * It updates sz to be the size of 
   */
  void getExplanationFor( Node n, Node vn, std::vector< Node >& exp, SygusInvarianceTest& et, Node vnr, unsigned& sz );
  void getExplanationFor( Node n, Node vn, std::vector< Node >& exp, SygusInvarianceTest& et );
private:
  /** sygus term database associated with this utility */
  TermDbSygus * d_tdb;
  /** Helper function for getExplanationFor */
  void getExplanationFor( TermRecBuild& trb, Node n, Node vn, std::vector< Node >& exp, std::map< TypeNode, int >& var_count,
                          SygusInvarianceTest& et, Node vnr, Node& vnr_exp, int& sz );
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_EXPLAIN_H */
