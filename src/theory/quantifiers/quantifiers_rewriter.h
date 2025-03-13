/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include "options/quantifiers_options.h"
#include "proof/trust_node.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {

class Options;
class TConvProofGenerator;
class CDProof;

namespace theory {

class Rewriter;

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
  /**
   * Term processing (e.g. simplifying terms based on ITE lifting,
   * eliminating extended arithmetic symbols).
   */
  COMPUTE_PROCESS_TERMS,
  /** Prenexing */
  COMPUTE_PRENEX,
  /** Variable elimination */
  COMPUTE_VAR_ELIMINATION,
  /** Datatype variable expansion */
  COMPUTE_DT_VAR_EXPAND,
  /** Conditional splitting */
  COMPUTE_COND_SPLIT,
  /**
   * Apply the extended rewriter to quantified formula bodies. This step
   * must come last, since it may invert other steps above, e.g. conditional
   * splitting.
   */
  COMPUTE_EXT_REWRITE,
  /** Placeholder for end of steps */
  COMPUTE_LAST
};
std::ostream& operator<<(std::ostream& out, RewriteStep s);

class QuantifiersRewriter : public TheoryRewriter
{
 public:
  QuantifiersRewriter(NodeManager* nm, Rewriter* r, const Options& opts);
  /** Pre-rewrite n */
  RewriteResponse preRewrite(TNode in) override;
  /** Post-rewrite n */
  RewriteResponse postRewrite(TNode in) override;

  /**
   * Rewrite n based on the proof rewrite rule id.
   * @param id The rewrite rule.
   * @param n The node to rewrite.
   * @return The rewritten version of n based on id, or Node::null() if n
   * cannot be rewritten.
   */
  Node rewriteViaRule(ProofRewriteRule id, const Node& n) override;

  static bool isLiteral( Node n );
  //-------------------------------------variable elimination utilities
  /** is variable elimination
   *
   * Returns true if v is not a subterm of s, and the type of s is the same as
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
  bool getVarElimLit(Node body,
                     Node n,
                     bool pol,
                     std::vector<Node>& args,
                     std::vector<Node>& vars,
                     std::vector<Node>& subs,
                     CDProof* cdp = nullptr) const;
  /**
   * Get variable eliminate for an equality based on theory-specific reasoning.
   */
  Node getVarElimEq(Node lit,
                    const std::vector<Node>& args,
                    Node& var,
                    CDProof* cdp = nullptr) const;
  /** variable eliminate for real equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  Node getVarElimEqReal(Node lit,
                        const std::vector<Node>& args,
                        Node& var,
                        CDProof* cdp = nullptr) const;
  /** variable eliminate for bit-vector equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  Node getVarElimEqBv(Node lit,
                      const std::vector<Node>& args,
                      Node& var,
                      CDProof* cdp = nullptr) const;
  /** variable eliminate for string equalities
   *
   * If this returns a non-null value ret, then var is updated to a member of
   * args, lit is equivalent to ( var = ret ).
   */
  Node getVarElimEqString(Node lit,
                          const std::vector<Node>& args,
                          Node& var,
                          CDProof* cdp = nullptr) const;
  /** get variable elimination
   *
   * If there exists an n with some polarity in body, and entails a literal that
   * corresponds to a variable elimination for some v via the above method
   * getVarElimLit, we return true. In this case, we update args/vars/subs
   * based on eliminating v.
   *
   * The vector lits is populated with the literals that imply each
   * vars[i]==subs[i].
   *
   * For simplicity, this method will only add a single element to
   * vars/subs/lits.
   *
   * note: for the sake of proofs, we require that lits[0] is *equivalent*
   * to (= vars[0] subs[0]).
   */
  bool getVarElim(Node body,
                  std::vector<Node>& args,
                  std::vector<Node>& vars,
                  std::vector<Node>& subs,
                  std::vector<Node>& lits,
                  CDProof* cdp = nullptr) const;
  /** has variable elimination
   *
   * Returns true if n asserted with polarity pol entails a literal for
   * which variable elimination is possible.
   */
  bool hasVarElim(Node n, bool pol, std::vector<Node>& args) const;
  /** compute variable elimination inequality
   *
   * This method eliminates variables from the body of quantified formula
   * "body" using (global) reasoning about inequalities. In particular, if there
   * exists a variable x that only occurs in body or annotation qa in literals
   * of the form x>=t with a fixed polarity P, then we may drop all such
   * literals. For example, note that:
   *   forall xy. x>y OR P(y) is equivalent to forall y. P(y).
   *
   * In the case that a variable x from args can be eliminated in this way,
   * we remove x from args and return the result of removing all literals
   * involving x from body.
   */
  Node getVarElimIneq(Node body,
                      std::vector<Node>& args,
                      QAttributes& qa) const;
  //-------------------------------------end variable elimination utilities
  /**
   * Compute miniscoping in quantified formula q with attributes in qa.
   */
  Node computeMiniscoping(Node q,
                          QAttributes& qa,
                          bool miniscopeConj,
                          bool miniscopeFv) const;
  Node computeAggressiveMiniscoping(std::vector<Node>& args, Node body) const;
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
  Node computePrenex(Node q,
                     Node body,
                     std::vector<Node>& args,
                     std::vector<Node>& nargs,
                     bool pol,
                     bool prenexAgg) const;
  Node computeSplit(std::vector<Node>& args, Node body, QAttributes& qa) const;

  static bool isPrenexNormalForm(Node n);
  Node mkForAll(const std::vector<Node>& args,
                Node body,
                QAttributes& qa) const;
  Node mkForall(const std::vector<Node>& args,
                Node body,
                bool marked = false) const;
  Node mkForall(const std::vector<Node>& args,
                Node body,
                std::vector<Node>& iplc,
                bool marked = false) const;
  /** Compute if q is a standard quantified formula based on the options */
  static bool isStandard(const Node& q, const Options& opts);
  /**
   * Compute if a quantified formula with the given attributes is standard
   * based on the options.
   */
  static bool isStandard(QAttributes& qa, const Options& opts);

  /**
   * @param q The quantified formula to rewrite.
   * @param pg If provided, stores a set of small step rewrites that suffice
   * to show that q rewrites to the returned quantified formula.
   * @return the result of rewriting q.
   */
  Node computeRewriteBody(const Node& q,
                          TConvProofGenerator* pg = nullptr) const;
  /**
   * compute datatype tester expansion, which implements
   * ProofRewriteRule::MACRO_QUANT_DT_VAR_EXPAND.
   *
   * @param nm Pointer to node manager.
   * @param q The quantified formula to rewrite.
   * @param index The index of the variable which we split on.
   * @return The (possibly rewritten) form of q.
   */
  static Node computeDtVarExpand(NodeManager* nm, const Node& q, size_t& index);

 private:
  /**
   * Do trivial merging of the prenex of quantified formula q, e.g.
   * (forall ((x Int)) (forall ((y Int)) (P x y))) --->
   * (forall ((x Int) (y Int)) (P x y)).
   * This is done until fixed point.
   *
   * @param q The quantified formula to prenex.
   * @param checkStd If true, we do not merge prenex for any non-standard
   * quantified formula
   * @param rmDup If true, we remove duplicate variables.
   * @return The result of merging prenex in q.
   */
  Node mergePrenex(const Node& q, bool checkStd, bool rmDup);
  /**
   * Helper method for getVarElim, called when n has polarity pol in body.
   */
  bool getVarElimInternal(Node body,
                          Node n,
                          bool pol,
                          std::vector<Node>& args,
                          std::vector<Node>& vars,
                          std::vector<Node>& subs,
                          std::vector<Node>& lits,
                          CDProof* cdp = nullptr) const;
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
  /**
   * Returns a node retBody such that q of the form
   *   forall args. body
   * is equivalent to:
   *   forall args. retBody
   *
   * @param q The original quantified formula we are processing
   * @param args The bound variables of q
   * @param body The subformula of the body of q we are processing
   * @param cache Cache from terms to their processed form
   * @param iteLiftMode The mode for lifting ITEs from body.
   */
  Node computeProcessTerms2(const Node& q,
                            const std::vector<Node>& args,
                            Node body,
                            std::map<Node, Node>& cache,
                            options::IteLiftQuantMode iteLiftMode,
                            TConvProofGenerator* pg) const;
  void computeDtTesterIteSplit(Node n,
                               std::map<Node, Node>& pcons,
                               std::map<Node, std::map<int, Node> >& ncons,
                               std::vector<Node>& conj) const;

  //-------------------------------------variable elimination
  /** compute variable elimination
   *
   * This computes variable elimination rewrites for a body of a quantified
   * formula with bound variables args. This method updates args to args' and
   * returns a node body' such that (forall args. body) is equivalent to
   * (forall args'. body'). An example of a variable elimination rewrite is:
   *   forall xy. x != a V P( x,y ) ---> forall y. P( a, y )
   */
  Node computeVarElimination(Node body,
                             std::vector<Node>& args,
                             QAttributes& qa) const;
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
  Node computeCondSplit(Node body,
                        const std::vector<Node>& args,
                        QAttributes& qa) const;
  //-------------------------------------end conditional splitting
  //------------------------------------- process terms
  /** compute process terms
   *
   * This takes as input a quantified formula q with attributes qa whose
   * bound variables are args, and whose body is body.
   *
   * This rewrite eliminates problematic terms from the bodies of
   * quantified formulas, which includes performing:
   * - Certain cases of ITE lifting,
   * - Elimination of select over store,
   * - Elimination of shadowed variables.
   */
  Node computeProcessTerms(const Node& q,
                           const std::vector<Node>& args,
                           Node body,
                           QAttributes& qa,
                           TConvProofGenerator* pg = nullptr) const;
  //------------------------------------- end process terms
  //------------------------------------- extended rewrite
  /** compute extended rewrite
   *
   * This returns the result of applying the extended rewriter on the body
   * of quantified formula q with attributes qa.
   */
  Node computeExtendedRewrite(TNode q, const QAttributes& qa) const;
  //------------------------------------- end extended rewrite
  /**
   * Return true if we should do operation computeOption on quantified formula
   * q with attributes qa.
   */
  bool doOperation(Node q, RewriteStep computeOption, QAttributes& qa) const;
  /** Whether we should miniscope based on conjunctions based on option */
  static bool doMiniscopeConj(const Options& opts);
  /** Whether we should miniscope based on free variables based on option */
  static bool doMiniscopeFv(const Options& opts);
  /**
   * Return the rewritten form of q after applying operator computeOption to it.
   */
  Node computeOperation(Node q,
                        RewriteStep computeOption,
                        QAttributes& qa) const;
  /** Pointer to rewriter, used for computeExtendedRewrite above */
  Rewriter* d_rewriter;
  /** Reference to the options */
  const Options& d_opts;
}; /* class QuantifiersRewriter */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */
