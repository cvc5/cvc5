/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter for the theory of (co)inductive datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__DATATYPES_REWRITER_H
#define CVC5__THEORY__DATATYPES__DATATYPES_REWRITER_H

#include "theory/evaluator.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {

class Options;

namespace theory {
namespace datatypes {

/**
 * The rewriter for datatypes. An invariant of the rewriter is that
 * postRewrite/preRewrite should not depend on the options, in particular,
 * they should not depend on whether shared selectors are enabled. Thus,
 * they should not use DTypeConstructor::getSelectorInternal. Instead,
 * the conversion from external to internal selectors is done in
 * expandDefinition. This invariant ensures that the rewritten form of a node
 * does not mix multiple option settings, which would lead to e.g. shared
 * selectors being used in an SolverEngine instance where they are disabled.
 */
class DatatypesRewriter : public TheoryRewriter
{
 public:
  DatatypesRewriter(Evaluator* sygusEval, const Options& opts);
  RewriteResponse postRewrite(TNode in) override;
  RewriteResponse preRewrite(TNode in) override;

  /** normalize codatatype constant
   *
   * This returns the normal form of the codatatype constant n. This runs a
   * DFA minimization algorithm based on the private functions below.
   *
   * In particular, we first call collectRefs to setup initial information
   * about what terms occur in n. Then, we run a DFA minimization algorithm to
   * partition these subterms in equivalence classes. Finally, we call
   * normalizeCodatatypeConstantEqc to construct the normalized codatatype
   * constant that is equivalent to n.
   */
  static Node normalizeCodatatypeConstant(Node n);
  /** normalize constant
   *
   * This method returns the normal form of n, which calls the above function
   * on all top-level codatatype subterms of n.
   */
  static Node normalizeConstant(Node n);
  /**
   * Expand an APPLY_SELECTOR term n, return its expanded form. If n is
   *   (APPLY_SELECTOR selC x)
   * its expanded form is
   *   (APPLY_SELECTOR selC' x)
   * where selC' is the internal selector function for selC (a shared selector
   * if sharedSel is true).
   * Note that we do not introduce an uninterpreted function here, e.g. to
   * handle when the selector is misapplied. This is because it suffices to
   * reason about the original selector term e.g. via congruence.
   */
  static Node expandApplySelector(Node n, bool sharedSel);
  /**
   * Expand a match term into its definition.
   * For example
   *   (MATCH x (((APPLY_CONSTRUCTOR CONS y z) z) (APPLY_CONSTRUCTOR NIL x)))
   * returns
   *   (ITE (APPLY_TESTER CONS x) (APPLY_SELECTOR x) x)
   */
  static Node expandMatch(Node n);
  /** expand defintions */
  TrustNode expandDefinition(Node n) override;

 private:
  /** rewrite constructor term in */
  static RewriteResponse rewriteConstructor(TNode in);
  /** rewrite selector term in */
  static RewriteResponse rewriteSelector(TNode in);
  /** rewrite tester term in */
  static RewriteResponse rewriteTester(TNode in);
  /** rewrite updater term in */
  static RewriteResponse rewriteUpdater(TNode in);

  /** collect references
   *
   * This function, given as input a codatatype term n, collects the necessary
   * information for constructing a (canonical) codatatype constant that is
   * equivalent to n if one exists, or null otherwise.
   *
   * In particular it returns a term ret such that all non-codatatype datatype
   * subterms of n are replaced by a constant that is equal to them via a
   * (mutually) recursive call to normalizeConstant above. Additionally, this
   * function replaces references to mu-binders with fresh variables.
   * In detail, mu-terms are represented by uninterpreted constants of datatype
   * type that carry their Debruijn index.
   *
   * Consider the example of a codatatype representing a stream of integers:
   *   Stream := cons( head : Int, tail : Stream )
   * The stream 1,0,1,0,1,0... when written in mu-notation is the term:
   *   mu x. cons( 1, mu y. cons( 0, x ) )
   * This is represented in cvc5 by the Node:
   *   cons( 1, cons( 0, c[1] ) )
   * where c[1] is a uninterpreted constant datatype with Debruijn index 1,
   * indicating that c[1] is nested underneath 1 level on the path to the
   * term which it binds. On the other hand, the stream 1,0,0,0,0,... is
   * represented by the codatatype term:
   *   cons( 1, cons( 0, c[0] ) )
   *
   * Subterms that are references to mu-binders in n are replaced by a new
   * variable. If n contains any subterm that is a reference to a mu-binder not
   * bound in n, then we return null. For example we return null when n is:
   *   cons( 1, cons( 0, c[2] ) )
   * since c[2] is not bound by this codatatype term.
   *
   * All valid references to mu-binders are replaced by a variable that is
   * unique for the term it references. For example, for the infinite tree
   * codatatype: Tree : node( data : Int, left : Tree, right : Tree ) If n is
   * the term: node( 0, c[0], node( 1, c[0], c[1] ) ) then the return value ret
   * of this function is: node( 0, x, node( 1, y, x ) ) where x refers to the
   * root of the term and y refers to the right tree of the root.
   *
   * The argument sk stores the current set of node that we are traversing
   * beneath. The argument rf_pending stores, for each node that we are
   * traversing beneath either null or the free variable that we are using to
   * refer to its mu-binder. The remaining arguments store information that is
   * relevant when performing normalization of n using the value of ret:
   *
   * rf : maps subterms of n to the corresponding term in ret for all subterms
   * where the corresponding term in ret is different.
   * terms : stores all subterms of ret.
   * cdts : for each term t in terms, stores whether t is a codatatype.
   */
  static Node collectRef(Node n,
                         std::vector<Node>& sk,
                         std::map<Node, Node>& rf,
                         std::vector<Node>& rf_pending,
                         std::vector<Node>& terms,
                         std::map<Node, bool>& cdts);
  /** normalize codatatype constant eqc
   *
   * This recursive function returns a codatatype constant that is equivalent to
   * n based on a pre-computed partition of the subterms of n into equivalence
   * classes, as stored in the mapping eqc, which maps the subterms of n to
   * equivalence class ids. The arguments eqc_stack and depth store information
   * about the traversal in a term we have recursed, where
   *
   * eqc_stack : maps the depth of each term we have traversed to its
   * equivalence class id. depth : the number of levels which we have traversed.
   */
  static Node normalizeCodatatypeConstantEqc(Node n,
                                             std::map<int, int>& eqc_stack,
                                             std::map<Node, int>& eqc,
                                             int depth);
  /** replace debruijn
   *
   * This function, given codatatype term n, returns a node
   * where all subterms of n that have Debruijn indices that refer to a
   * term of input depth are replaced by orig. For example, for the infinite
   * Tree datatype, replaceDebruijn( node( 0, c[0], node( 1, c[0], c[1] ) ), t,
   * Tree, 0 ) returns node( 0, t, node( 1, c[0], t ) ).
   */
  static Node replaceDebruijn(Node n,
                              Node orig,
                              TypeNode orig_tn,
                              unsigned depth);

  /** Sygus to builtin eval
   *
   * This method returns the rewritten form of (DT_SYGUS_EVAL n args). Notice
   * that n does not necessarily need to be a constant.
   *
   * It does so by (1) converting constant subterms of n to builtin terms and
   * evaluating them on the arguments args, (2) unfolding non-constant
   * applications of sygus constructors in n with respect to args and (3)
   * converting all other non-constant subterms of n to applications of
   * DT_SYGUS_EVAL.
   *
   * For example, if
   *   n = C_+( C_*( C_x(), C_y() ), n' ), and args = { 3, 4 }
   * where n' is a variable, then this method returns:
   *   12 + (DT_SYGUS_EVAL n' 3 4)
   * Notice that the subterm C_*( C_x(), C_y() ) is converted to its builtin
   * equivalent x*y and evaluated under the substition { x -> 3, y -> 4 } giving
   * 12. The subterm n' is non-constant and thus we return its evaluation under
   * 3,4, giving the term (DT_SYGUS_EVAL n' 3 4). Since the top-level
   * constructor is C_+, these terms are added together to give the result.
   */
  Node sygusToBuiltinEval(Node n, const std::vector<Node>& args);
  /** Pointer to the evaluator, used as an optimization for the above method */
  Evaluator* d_sygusEval;
  /** Reference to the options */
  const Options& d_opts;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DATATYPES__DATATYPES_REWRITER_H */
