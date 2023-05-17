/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Higher-order term database class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__HO_TERM_DATABASE_H
#define CVC5__THEORY__QUANTIFIERS__HO_TERM_DATABASE_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/term_database.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Higher-order term database, which extends the normal term database based on
 * techniques from Barbosa et al CADE 2019.
 */
class HoTermDb : public TermDb
{
 public:
  HoTermDb(Env& env, QuantifiersState& qs, QuantifiersRegistry& qr);
  ~HoTermDb();
  /** identify */
  std::string identify() const override { return "HoTermDb"; }
  /** get higher-order type match predicate
   *
   * This predicate is used to force certain functions f of type tn to appear as
   * first-class representatives in the quantifier-free UF solver. For a typical
   * use case, we call getHoTypeMatchPredicate which returns a fresh predicate
   * P of type (tn -> Bool). Then, we add P( f ) as a lemma.
   */
  static Node getHoTypeMatchPredicate(TypeNode tn);

 private:
  /**
   * Reset internal, called when reset(e) is called. Returning false will cause
   * the overall reset to terminate early, returning false.
   */
  bool resetInternal(Theory::Effort e) override;
  /** Performs merging of term indices based on higher-order reasoning */
  bool finishResetInternal(Theory::Effort e) override;
  /** add term higher-order
   *
   * This registers additional terms corresponding to (possibly multiple)
   * purifications of a higher-order term n.
   *
   * Consider the example:
   *    g : Int -> Int, f : Int x Int -> Int
   *    constraints: (@ f 0) = g, (f 0 1) = (@ (@ f 0) 1) = 3
   *    pattern: (g x)
   * where @ is HO_APPLY.
   * We have that (g x){ x -> 1 } is an E-match for (@ (@ f 0) 1).
   * With the standard registration in addTerm, we construct term indices for
   *   f, g, @ : Int x Int -> Int, @ : Int -> Int.
   * However, to match (g x) with (@ (@ f 0) 1), we require that
   *   [1] -> (@ (@ f 0) 1)
   * is an entry in the term index of g. To do this, we maintain a term
   * index for a fresh variable pfun, the purification variable for
   * (@ f 0). Thus, we register the term (pfun 1) in the call to this function
   * for (@ (@ f 0) 1). This ensures that, when processing the equality
   * (@ f 0) = g, we merge the term indices of g and pfun. Hence, the entry
   *   [1] -> (@ (@ f 0) 1)
   * is added to the term index of g, assuming g is the representative of
   * the equivalence class of g and pfun.
   *
   * Above, we set d_hoFunOpPurify[(@ f 0)] = pfun, and
   * d_hoPurifyToTerm[(pfun 1)] = (@ (@ f 0) 1).
   */
  void addTermInternal(Node n) override;
  /** Get operators that we know are equivalent to f */
  void getOperatorsFor(TNode f, std::vector<TNode>& ops) override;
  /** get the chosen representative for operator op */
  Node getOperatorRepresentative(TNode op) const override;
  /** check if we are in conflict based on congruent terms a and b */
  bool checkCongruentDisequal(TNode a,
                              TNode b,
                              std::vector<Node>& exp) override;
  //------------------------------higher-order term indexing
  /**
   * Map from non-variable function terms to the operator used to purify it in
   * this database. For details, see addTermHo.
   */
  std::map<Node, Node> d_hoFunOpPurify;
  /**
   * Map from terms to the term that they purified. For details, see addTermHo.
   */
  std::map<Node, Node> d_hoPurifyToTerm;
  /**
   * Map from terms in the domain of the above map to an equality between that
   * term and its range in the above map.
   */
  std::map<Node, Node> d_hoPurifyToEq;
  /** a map from matchable operators to their representative */
  std::map<TNode, TNode> d_hoOpRep;
  /** for each representative matchable operator, the list of other matchable
   * operators in their equivalence class */
  std::map<TNode, std::vector<TNode> > d_hoOpSlaves;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__HO_TERM_DATABASE_H */
