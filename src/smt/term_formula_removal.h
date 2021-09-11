/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Removal of term formulas.
 */

#include "cvc5_private.h"

#pragma once

#include <unordered_set>
#include <vector>

#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "expr/term_context.h"
#include "proof/trust_node.h"
#include "util/hash.h"

namespace cvc5 {

class LazyCDProof;
class ProofNodeManager;
class TConvProofGenerator;

class RemoveTermFormulas {
 public:
  RemoveTermFormulas(context::UserContext* u, ProofNodeManager* pnm = nullptr);
  ~RemoveTermFormulas();

  /**
   * By introducing skolem variables, this function removes all occurrences of:
   * (1) term ITEs,
   * (2) terms of type Boolean that are not Boolean term variables,
   * (3) lambdas, and
   * (4) Hilbert choice expressions.
   * from assertions.
   * All additional assertions are pushed into assertions. iteSkolemMap
   * contains a map from introduced skolem variables to the index in
   * assertions containing the new definition created in conjunction
   * with that skolem variable.
   *
   * As an example of (1):
   *   f( (ite C 0 1)) = 2
   * becomes
   *   f( k ) = 2 ^ ite( C, k=0, k=1 )
   *
   * As an example of (2):
   *   g( (and C1 C2) ) = 3
   * becomes
   *   g( k ) = 3 ^ ( k <=> (and C1 C2) )
   *
   * As an example of (3):
   *   (lambda x. t[x]) = f
   * becomes
   *   (forall x. k(x) = t[x]) ^ k = f
   * where k is a fresh skolem function.
   * This is sometimes called "lambda lifting"
   *
   * As an example of (4):
   *   (witness x. P( x ) ) = t
   * becomes
   *   P( k ) ^ k = t
   * where k is a fresh skolem constant.
   *
   * With reportDeps true, report reasoning dependences to the proof
   * manager (for unsat cores).
   *
   * @param assertion The assertion to remove term formulas from
   * @param newAsserts The new assertions corresponding to axioms for newly
   * introduced skolems.
   * @param newSkolems The skolems corresponding to each of the newAsserts.
   * @param fixedPoint Whether to run term formula removal on the lemmas in
   * newAsserts. This adds new assertions to this vector until a fixed
   * point is reached. When this option is true, all lemmas in newAsserts
   * have all term formulas removed.
   * @return a trust node of kind TrustNodeKind::REWRITE whose
   * right hand side is assertion after removing term formulas, and the proof
   * generator (if provided) that can prove the equivalence.
   */
  TrustNode run(TNode assertion,
                std::vector<TrustNode>& newAsserts,
                std::vector<Node>& newSkolems,
                bool fixedPoint = false);
  /**
   * Same as above, but does not track lemmas, and does not run to fixed point.
   * The relevant lemmas can be extracted by the caller later using getSkolems
   * and getLemmaForSkolem.
   */
  TrustNode run(TNode assertion);
  /**
   * Same as above, but transforms a lemma, returning a LEMMA trust node that
   * proves the same formula as lem with term formulas removed.
   */
  TrustNode runLemma(TrustNode lem,
                     std::vector<TrustNode>& newAsserts,
                     std::vector<Node>& newSkolems,
                     bool fixedPoint = false);

  /**
   * Get proof generator that is responsible for all proofs for removing term
   * formulas from nodes. When proofs are enabled, the returned trust node
   * of the run method use this proof generator (the trust nodes in newAsserts
   * do not use this generator).
   */
  ProofGenerator* getTConvProofGenerator();

  /**
   * Get axiom for term n. This returns the axiom that this class uses to
   * eliminate the term n, which is determined by its top-most symbol. For
   * example, if n is (ite n1 n2 n3), this returns the formula:
   *   (ite n1 (= (ite n1 n2 n3) n2) (= (ite n1 n2 n3) n3))
   */
  static Node getAxiomFor(Node n);

 private:
  typedef context::CDInsertHashMap<
      std::pair<Node, uint32_t>,
      Node,
      PairHashFunction<Node, uint32_t, std::hash<Node>>>
      TermFormulaCache;
  /** term formula removal cache
   *
   * This stores the results of term formula removal for inputs to the run(...)
   * function below, where the integer in the pair we hash on is the
   * result of cacheVal below.
   */
  TermFormulaCache d_tfCache;

  /** skolem cache
   *
   * This is a cache that maps terms to the skolem we use to replace them.
   *
   * Notice that this cache is necessary in addition to d_tfCache, since
   * we should use the same skolem to replace terms, regardless of the input
   * arguments to run(...). For example:
   *
   * ite( G, a, b ) = c ^ forall x. P( ite( G, a, b ), x )
   *
   * should be processed to:
   *
   * k = c ^ forall x. P( k, x ) ^ ite( G, k=a, k=b )
   *
   * where notice
   *   d_skolem_cache[ite( G, a, b )] = k, and
   *   d_tfCache[<ite( G, a, b ),0>] = d_tfCache[<ite( G, a, b ),1>] = k.
   */
  context::CDInsertHashMap<Node, Node> d_skolem_cache;

  /** gets the skolem for node
   *
   * This returns the d_skolem_cache value for node, if it exists as a key
   * in the above map, or the null node otherwise.
   */
  inline Node getSkolemForNode(Node node) const;

  /** Pointer to a proof node manager */
  ProofNodeManager* d_pnm;
  /**
   * A proof generator for the term conversion.
   */
  std::unique_ptr<TConvProofGenerator> d_tpg;
  /**
   * A proof generator for skolems we introduce that are based on axioms that
   * this class is responsible for.
   */
  std::unique_ptr<LazyCDProof> d_lp;
  /**
   * The remove term formula context, which computes hash values for term
   * contexts.
   */
  RtfTermContext d_rtfc;

  /**
   * Removes terms of the forms described above from formula assertion.
   * All additional assertions and skolems are pushed into newAsserts and
   * newSkolems, which are always of the same length.
   *
   * This uses a term-context-sensitive stack to process assertion. It returns
   * the version of assertion with all term formulas removed.
   */
  Node runInternal(TNode assertion,
                   std::vector<TrustNode>& newAsserts,
                   std::vector<Node>& newSkolems);
  /**
   * This is called on curr of the form (t, val) where t is a term and val is
   * a term context identifier computed by RtfTermContext. If curr should be
   * replaced by a skolem, this method returns this skolem k. If this was the
   * first time that t was encountered, we set newLem to the lemma for the
   * skolem that axiomatizes k.
   *
   * Otherwise, if t should not be replaced in the term context, this method
   * returns the null node.
   */
  Node runCurrent(std::pair<Node, uint32_t>& curr, TrustNode& newLem);

  /** Whether proofs are enabled */
  bool isProofEnabled() const;
};/* class RemoveTTE */

}  // namespace cvc5
