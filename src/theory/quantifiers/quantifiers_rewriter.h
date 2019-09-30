/*********************                                                        */
/*! \file quantifiers_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of inductive quantifiers
 **
 ** Rewriter for the theory of inductive quantifiers.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H
#define CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct QAttributes;

class QuantifiersRewriter {
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
   * If n asserted with polarity pol is equivalent to an equality of the form
   * v = s for some v in args, where isVariableElim( v, s ) holds, then this
   * method removes v from args, adds v to vars, adds s to subs, and returns
   * true. Otherwise, it returns false.
   */
  static bool getVarElimLit(Node n,
                            bool pol,
                            std::vector<Node>& args,
                            std::vector<Node>& vars,
                            std::vector<Node>& subs);
  /** variable eliminate for bit-vector equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  static Node getVarElimLitBv(Node lit,
                              const std::vector<Node>& args,
                              Node& var);
  /** variable eliminate for string equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  static Node getVarElimLitString(Node lit,
                                  const std::vector<Node>& args,
                                  Node& var);
  /** get variable elimination
   *
   * If n asserted with polarity pol entails a literal lit that corresponds
   * to a variable elimination for some v via the above method, we return true.
   * In this case, we update args/vars/subs based on eliminating v.
   */
  static bool getVarElim(Node n,
                         bool pol,
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
  static int getPurifyIdLit2(Node n, std::map<Node, int>& visited);
  static bool addCheckElimChild(std::vector<Node>& children,
                                Node c,
                                Kind k,
                                std::map<Node, bool>& lit_pol,
                                bool& childrenChanged);
  static void addNodeToOrBuilder(Node n, NodeBuilder<>& t);
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
                                   bool hasPol,
                                   bool pol,
                                   std::map<Node, bool>& currCond,
                                   int nCurrCond,
                                   std::map<Node, Node>& cache,
                                   std::map<Node, Node>& icache,
                                   std::vector<Node>& new_vars,
                                   std::vector<Node>& new_conds,
                                   bool elimExtArith);
  static void computeDtTesterIteSplit(
      Node n,
      std::map<Node, Node>& pcons,
      std::map<Node, std::map<int, Node> >& ncons,
      std::vector<Node>& conj);
  /** datatype expand
   *
   * If v occurs in args and has a datatype type whose index^th constructor is
   * C, this method returns a node of the form C( x1, ..., xn ), removes v from
   * args and adds x1...xn to args.
   */
  static Node datatypeExpand(unsigned index, Node v, std::vector<Node>& args);

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
 public:
  static Node computeElimSymbols( Node body );
  static Node computeMiniscoping( std::vector< Node >& args, Node body, QAttributes& qa );
  static Node computeAggressiveMiniscoping( std::vector< Node >& args, Node body );
  //cache is dependent upon currCond, icache is not, new_conds are negated conditions
  static Node computeProcessTerms( Node body, std::vector< Node >& new_vars, std::vector< Node >& new_conds, Node q, QAttributes& qa );
  static Node computePrenex( Node body, std::vector< Node >& args, std::vector< Node >& nargs, bool pol, bool prenexAgg );
  static Node computePrenexAgg( Node n, bool topLevel, std::map< unsigned, std::map< Node, Node > >& visited );
  static Node computeSplit( std::vector< Node >& args, Node body, QAttributes& qa );
private:
  enum{
    COMPUTE_ELIM_SYMBOLS = 0,
    COMPUTE_MINISCOPING,
    COMPUTE_AGGRESSIVE_MINISCOPING,
    COMPUTE_PROCESS_TERMS,
    COMPUTE_PRENEX,
    COMPUTE_VAR_ELIMINATION,
    COMPUTE_COND_SPLIT,
    COMPUTE_LAST
  };
  static Node computeOperation( Node f, int computeOption, QAttributes& qa );
public:
  static RewriteResponse preRewrite(TNode in);
  static RewriteResponse postRewrite(TNode in);
  static inline void init() {}
  static inline void shutdown() {}
private:
  /** options */
  static bool doOperation( Node f, int computeOption, QAttributes& qa );
private:
  static Node preSkolemizeQuantifiers(Node n, bool polarity, std::vector< TypeNode >& fvTypes, std::vector<TNode>& fvs);
public:
  static Node rewriteRewriteRule( Node r );
  static bool containsQuantifiers( Node n );
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
   */
  static Node preprocess( Node n, bool isInst = false );
  static Node mkForAll( std::vector< Node >& args, Node body, QAttributes& qa );
  static Node mkForall( std::vector< Node >& args, Node body, bool marked = false );
  static Node mkForall( std::vector< Node >& args, Node body, std::vector< Node >& iplc, bool marked = false );
};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */


