/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alpha equivalence checking.
 */

#include "cvc5_private.h"

#ifndef CVC5__ALPHA_EQUIVALENCE_H
#define CVC5__ALPHA_EQUIVALENCE_H

#include "expr/term_canonize.h"
#include "proof/eager_proof_generator.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * This trie stores a trie for each multi-set of types. For each term t
 * registered to this node, we store t in the appropriate
 * AlphaEquivalenceTypeNode trie. For example, if t contains 2 free variables of
 * type T1 and 3 free variables of type T2, then it is stored at
 * d_children[T1][2].d_children[T2][3].
 */
class AlphaEquivalenceTypeNode {
  using NodeMap = context::CDHashMap<Node, Node>;

 public:
  AlphaEquivalenceTypeNode(context::Context* c);
  /** children of this node */
  std::map<std::pair<TypeNode, size_t>,
           std::unique_ptr<AlphaEquivalenceTypeNode>>
      d_children;
  /**
   * map from canonized quantifier bodies to a quantified formula whose
   * canonized body is that term.
   */
  NodeMap d_quant;
  /** register node
   *
   * This registers term q to this trie. The term t is the canonical form of
   * q, typs/typCount represent a multi-set of types of free variables in t.
   */
  Node registerNode(context::Context* c,
                    Node q,
                    Node t,
                    std::vector<TypeNode>& typs,
                    std::map<TypeNode, size_t>& typCount);
};

/**
 * Stores a database of quantified formulas, which computes alpha-equivalence.
 */
class AlphaEquivalenceDb
{
 public:
  AlphaEquivalenceDb(context::Context* c,
                     expr::TermCanonize* tc,
                     bool sortCommChildren);
  /** adds quantified formula q to this database
   *
   * This function returns a quantified formula q' that is alpha-equivalent to
   * q. If q' != q, then q' was previously added to this database via a call
   * to addTerm.
   */
  Node addTerm(Node q);
  /**
   * Add term with substitution, which additionally finds a set of terms such
   * that q' * subs is alpha-equivalent (possibly modulo rewriting) to q, where
   * q' is the return quantified formula.
   */
  Node addTermWithSubstitution(Node q,
                               std::vector<Node>& vars,
                               std::vector<Node>& subs);

 private:
  /**
   * Add term to the trie, where t is the canonized form of the body of
   * quantified formula q. Returns the quantified formula, if any, that already
   * had been added to this class, or q otherwise.
   */
  Node addTermToTypeTrie(Node t, Node q);
  /** The context we depend on */
  context::Context* d_context;
  /** a trie per # of variables per type */
  AlphaEquivalenceTypeNode d_ae_typ_trie;
  /** pointer to the term canonize utility */
  expr::TermCanonize* d_tc;
  /** whether to sort children of commutative operators during canonization. */
  bool d_sortCommutativeOpChildren;
  /**
   * Maps quantified formulas to variables map, used for tracking substitutions
   * in addTermWithSubstitution. The range in d_bvmap[q] contains the mapping
   * from canonical free variables to variables in q.
   */
  std::map<Node, std::map<Node, TNode> > d_bvmap;
};

/**
 * A quantifiers module that computes reductions based on alpha-equivalence,
 * using the above utilities.
 */
class AlphaEquivalence : protected EnvObj
{
 public:
  AlphaEquivalence(Env& env);
  ~AlphaEquivalence(){}
  /** reduce quantifier
   *
   * If non-null, its return value is a trust node containing the lemma
   * justifying why q is reducible.  This lemma is of the form ( q = q' ) where
   * q' is a quantified formula that was previously registered to this class via
   * a call to reduceQuantifier, and q and q' are alpha-equivalent.
   */
  TrustNode reduceQuantifier(Node q);

 private:
  /** a term canonizer */
  expr::TermCanonize d_termCanon;
  /** the database of quantified formulas registered to this class */
  AlphaEquivalenceDb d_aedb;
  /** An eager proof generator storing alpha equivalence proofs.*/
  std::unique_ptr<EagerProofGenerator> d_pfAlpha;
  /** Are proofs enabled for this object? */
  bool isProofEnabled() const;
};

}
}
}  // namespace cvc5::internal

#endif
