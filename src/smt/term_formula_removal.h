/*********************                                                        */
/*! \file term_formula_removal.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Removal of term formulas
 **
 ** Removal of term formulas.
 **/

#include "cvc4_private.h"

#pragma once

#include <unordered_map>
#include <vector>

#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/lazy_proof.h"
#include "expr/node.h"
#include "expr/term_context_stack.h"
#include "expr/term_conversion_proof_generator.h"
#include "theory/eager_proof_generator.h"
#include "theory/trust_node.h"
#include "util/bool.h"
#include "util/hash.h"

namespace CVC4 {

typedef std::unordered_map<Node, unsigned, NodeHashFunction> IteSkolemMap;

class RemoveTermFormulas {
 public:
  RemoveTermFormulas(context::UserContext* u);
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
   * @param reportDeps Used for unsat cores in the old proof infrastructure.
   * @return a trust node of kind TrustNodeKind::REWRITE whose
   * right hand side is assertion after removing term formulas, and the proof
   * generator (if provided) that can prove the equivalence.
   */
  theory::TrustNode run(Node assertion,
                        std::vector<theory::TrustNode>& newAsserts,
                        std::vector<Node>& newSkolems,
                        bool reportDeps = false);

  /**
   * Substitute under node using pre-existing cache.  Do not remove
   * any ITEs not seen during previous runs.
   */
  Node replace(TNode node) const;

  /** Returns true if e contains a term ite. */
  bool containsTermITE(TNode e) const;

  /** Garbage collects non-context dependent data-structures. */
  void garbageCollect();

  /**
   * Set proof node manager, which signals this class to enable proofs using the
   * given checker.
   */
  void setProofNodeManager(ProofNodeManager* pnm);

  /**
   * Get axiom for term n. This returns the axiom that this class uses to
   * eliminate the term n, which is determined by its top-most symbol. For
   * example, if n is (ite n1 n2 n3), this returns the formula:
   *   (ite n1 (= (ite n1 n2 n3) n2) (= (ite n1 n2 n3) n3))
   */
  static Node getAxiomFor(Node n);

 private:
  typedef context::CDInsertHashMap<
      std::pair<Node, int32_t>,
      Node,
      PairHashFunction<Node, int32_t, NodeHashFunction> >
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
  context::CDInsertHashMap<Node, Node, NodeHashFunction> d_skolem_cache;

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
  Node runInternal(Node assertion,
                   std::vector<theory::TrustNode>& newAsserts,
                   std::vector<Node>& newSkolems);
  /**
   * This is called on curr of the form (t, val) where t is a term and val is
   * a term context identifier computed by RtfTermContext. If curr should be
   * replaced by a skolem, this method returns this skolem k, adds k to
   * newSkolems and adds the axiom defining that skolem to newAsserts, where
   * runInternal is called on that axiom. Otherwise, this method returns the
   * null node.
   */
  Node runCurrent(std::pair<Node, uint32_t>& curr,
                  std::vector<theory::TrustNode>& newAsserts,
                  std::vector<Node>& newSkolems);
  /** Replace internal */
  Node replaceInternal(TCtxStack& ctx) const;

  /** Whether proofs are enabled */
  bool isProofEnabled() const;
};/* class RemoveTTE */

}/* CVC4 namespace */
