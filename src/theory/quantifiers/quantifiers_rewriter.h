/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter for the theory of inductive quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H

#include "proof/trust_node.h"
#include "theory/theory_rewriter.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

struct QAttributes;

/**
 * List of steps used by the quantifiers rewriter, details on these steps
 * can be found in the class below.
 */
enum RewriteStep
{
  /** Eliminate symbols (e.g. implies, xor) */
  COMPUTE_ELIM_SYMBOLS = 0,
  /** Miniscoping */
  COMPUTE_MINISCOPING,
  /** Aggressive miniscoping */
  COMPUTE_AGGRESSIVE_MINISCOPING,
  /** Apply the extended rewriter to quantified formula bodies */
  COMPUTE_EXT_REWRITE,
  /**
   * Term processing (e.g. simplifying terms based on ITE lifting,
   * eliminating extended arithmetic symbols).
   */
  COMPUTE_PROCESS_TERMS,
  /** Prenexing */
  COMPUTE_PRENEX,
  /** Variable elimination */
  COMPUTE_VAR_ELIMINATION,
  /** Conditional splitting */
  COMPUTE_COND_SPLIT,
  /** Placeholder for end of steps */
  COMPUTE_LAST
};
std::ostream& operator<<(std::ostream& out, RewriteStep s);

class QuantifiersRewriter : public TheoryRewriter
{
 public:
  static bool isLiteral( Node n );
  //-------------------------------------variable elimination utilities
  /** is variable elimination
   *
   * Returns true if v is not a subterm of s, and the type of s is a subtype of
   * the type of v.
   */
  static bool isVarElim(Node v, Node s);
  /** get variable elimination literal
   *
   * If n asserted with polarity pol in body, and is equivalent to an equality
   * of the form v = s for some v in args, where isVariableElim( v, s ) holds,
   * then this method removes v from args, adds v to vars, adds s to subs, and
   * returns true. Otherwise, it returns false.
   */
  static bool getVarElimLit(Node body,
                            Node n,
                            bool pol,
                            std::vector<Node>& args,
                            std::vector<Node>& vars,
                            std::vector<Node>& subs);
  /**
   * Get variable eliminate for an equality based on theory-specific reasoning.
   */
  static Node getVarElimEq(Node lit, const std::vector<Node>& args, Node& var);
  /** variable eliminate for real equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  static Node getVarElimEqReal(Node lit,
                               const std::vector<Node>& args,
                               Node& var);
  /** variable eliminate for bit-vector equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  static Node getVarElimEqBv(Node lit,
                             const std::vector<Node>& args,
                             Node& var);
  /** variable eliminate for string equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  static Node getVarElimEqString(Node lit,
                                 const std::vector<Node>& args,
                                 Node& var);
  /** get variable elimination
   *
   * If there exists an n with some polarity in body, and entails a literal that
   * corresponds to a variable elimination for some v via the above method
   * getVarElimLit, we return true. In this case, we update args/vars/subs
   * based on eliminating v.
   */
  static bool getVarElim(Node body,
                         std::vector<Node>& args,
                         std::vector<Node>& vars,
                         std::vector<Node>& subs);
  /** has variable elimination
   *
   * Returns true if n asserted with polarity pol entails a literal for
   * which variable elimination is possible.
   */
  static bool hasVarElim(Node n, bool pol, std::vector<Node>& args);
  /** compute variable elimination inequality
   *
   * This method eliminates variables from the body of quantified formula
   * "body" using (global) reasoning about inequalities. In particular, if there
   * exists a variable x that only occurs in body or annotation qa in literals
   * of the form x>=t with a fixed polarity P, then we may replace all such
   * literals with P. For example, note that:
   *   forall xy. x>y OR P(y) is equivalent to forall y. P(y).
   *
   * In the case that a variable x from args can be eliminated in this way,
   * we remove x from args, add x >= t1, ..., x >= tn to bounds, add false, ...,
   * false to subs, and return true.
   */
  static bool getVarElimIneq(Node body,
                             std::vector<Node>& args,
                             std::vector<Node>& bounds,
                             std::vector<Node>& subs,
                             QAttributes& qa);
  //-------------------------------------end variable elimination utilities
 private:
  /**
   * Helper method for getVarElim, called when n has polarity pol in body.
   */
  static bool getVarElimInternal(Node body,
                                 Node n,
                                 bool pol,
                                 std::vector<Node>& args,
                                 std::vector<Node>& vars,
                                 std::vector<Node>& subs);
  static int getPurifyIdLit2(Node n, std::map<Node, int>& visited);
  static bool addCheckElimChild(std::vector<Node>& children,
                                Node c,
                                Kind k,
                                std::map<Node, bool>& lit_pol,
                                bool& childrenChanged);
  static void addNodeToOrBuilder(Node n, NodeBuilder& t);
  static void computeArgs(const std::vector<Node>& args,
                          std::map<Node, bool>& activeMap,
                          Node n,
                          std::map<Node, bool>& visited);
  static void computeArgVec(const std::vector<Node>& args,
                            std::vector<Node>& activeArgs,
                            Node n);
  static void computeArgVec2(const std::vector<Node>& args,
                             std::vector<Node>& activeArgs,
                             Node n,
                             Node ipl);
  static Node computeProcessTerms2(Node body,
                                   std::map<Node, Node>& cache,
                                   std::vector<Node>& new_vars,
                                   std::vector<Node>& new_conds);
  static void computeDtTesterIteSplit(
      Node n,
      std::map<Node, Node>& pcons,
      std::map<Node, std::map<int, Node> >& ncons,
      std::vector<Node>& conj);

  //-------------------------------------variable elimination
  /** compute variable elimination
   *
   * This computes variable elimination rewrites for a body of a quantified
   * formula with bound variables args. This method updates args to args' and
   * returns a node body' such that (forall args. body) is equivalent to
   * (forall args'. body'). An example of a variable elimination rewrite is:
   *   forall xy. x != a V P( x,y ) ---> forall y. P( a, y )
   */
  static Node computeVarElimination(Node body,
                                    std::vector<Node>& args,
                                    QAttributes& qa);
  //-------------------------------------end variable elimination
  //-------------------------------------conditional splitting
  /** compute conditional splitting
   *
   * This computes conditional splitting rewrites for a body of a quantified
   * formula with bound variables args. It returns a body' that is equivalent
   * to body. We split body into a conjunction if variable elimination can
   * occur in one of the conjuncts. Examples of this are:
   *   ite( x=a, P(x), Q(x) ) ----> ( x!=a V P(x) ) ^ ( x=a V Q(x) )
   *   (x=a) = P(x) ----> ( x!=a V P(x) ) ^ ( x=a V ~P(x) )
   *   ( x!=a ^ P(x) ) V Q(x) ---> ( x!=a V Q(x) ) ^ ( P(x) V Q(x) )
   * where in each case, x can be eliminated in the first conjunct.
   */
  static Node computeCondSplit(Node body,
                               const std::vector<Node>& args,
                               QAttributes& qa);
  //-------------------------------------end conditional splitting
  //------------------------------------- process terms
  /** compute process terms
   *
   * This takes as input a quantified formula q with attributes qa whose
   * body is body.
   *
   * This rewrite eliminates problematic terms from the bodies of
   * quantified formulas, which includes performing:
   * - Certain cases of ITE lifting,
   * - Elimination of extended arithmetic functions like to_int/is_int/div/mod,
   * - Elimination of select over store.
   *
   * It may introduce new variables V into new_vars and new conditions C into
   * new_conds. It returns a node retBody such that q of the form
   *   forall X. body
   * is equivalent to:
   *   forall X, V. ( C => retBody )
   */
  static Node computeProcessTerms(Node body,
                                  std::vector<Node>& new_vars,
                                  std::vector<Node>& new_conds,
                                  Node q,
                                  QAttributes& qa);
  //------------------------------------- end process terms
  //------------------------------------- extended rewrite
  /** compute extended rewrite
   *
   * This returns the result of applying the extended rewriter on the body
   * of quantified formula q.
   */
  static Node computeExtendedRewrite(Node q);
  //------------------------------------- end extended rewrite
 public:
  static Node computeElimSymbols( Node body );
  /**
   * Compute miniscoping in quantified formula q with attributes in qa.
   */
  static Node computeMiniscoping(Node q, QAttributes& qa);
  static Node computeAggressiveMiniscoping( std::vector< Node >& args, Node body );
  /**
   * This function removes top-level quantifiers from subformulas of body
   * appearing with overall polarity pol. It adds quantified variables that
   * appear in positive polarity positions into args, and those at negative
   * polarity positions in nargs.
   *
   * If prenexAgg is true, we ensure that all top-level quantifiers are
   * eliminated from subformulas. This means that we must expand ITE and
   * Boolean equalities to ensure that quantifiers are at fixed polarities.
   *
   * For example, calling this function on:
   *   (or (forall ((x Int)) (P x z)) (not (forall ((y Int)) (Q y z))))
   * would return:
   *   (or (P x z) (not (Q y z)))
   * and add {x} to args, and {y} to nargs.
   */
  static Node computePrenex(Node q,
                            Node body,
                            std::unordered_set<Node>& args,
                            std::unordered_set<Node>& nargs,
                            bool pol,
                            bool prenexAgg);
  /**
   * Apply prenexing aggressively. Returns the prenex normal form of n.
   */
  static Node computePrenexAgg(Node n, std::map<Node, Node>& visited);
  static Node computeSplit( std::vector< Node >& args, Node body, QAttributes& qa );
private:
 static Node computeOperation(Node f,
                              RewriteStep computeOption,
                              QAttributes& qa);

public:
 RewriteResponse preRewrite(TNode in) override;
 RewriteResponse postRewrite(TNode in) override;

private:
  /** options */
 static bool doOperation(Node f, RewriteStep computeOption, QAttributes& qa);

private:
  static Node preSkolemizeQuantifiers(Node n, bool polarity, std::vector< TypeNode >& fvTypes, std::vector<TNode>& fvs);
public:
  static bool isPrenexNormalForm( Node n );
  /** preprocess
   *
   * This returns the result of applying simple quantifiers-specific
   * preprocessing to n, including but not limited to:
   * - rewrite rule elimination,
   * - pre-skolemization,
   * - aggressive prenexing.
   * The argument isInst is set to true if n is an instance of a previously
   * registered quantified formula. If this flag is true, we do not apply
   * certain steps like pre-skolemization since we know they will have no
   * effect.
   *
   * The result is wrapped in a trust node of kind TrustNodeKind::REWRITE.
   */
  static TrustNode preprocess(Node n, bool isInst = false);
  static Node mkForAll(const std::vector<Node>& args,
                       Node body,
                       QAttributes& qa);
  static Node mkForall(const std::vector<Node>& args,
                       Node body,
                       bool marked = false);
  static Node mkForall(const std::vector<Node>& args,
                       Node body,
                       std::vector<Node>& iplc,
                       bool marked = false);
}; /* class QuantifiersRewriter */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */
