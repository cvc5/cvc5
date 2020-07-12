/*********************                                                        */
/*! \file term_conversion_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term conversion proof generator utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H
#define CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/lazy_proof.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"

namespace CVC4 {

/** A policy for how rewrite steps are applied in TConvProofGenerator */
enum class TConvPolicy : uint32_t
{
  // steps are applied to fix-point, common use case is PfRule::REWRITE
  FIXPOINT,
  // steps are applied once at pre-rewrite, common use case is PfRule::SUBS
  ONCE,
};
/** Writes a term conversion policy name to a stream. */
std::ostream& operator<<(std::ostream& out, TConvPolicy tcpol);

/**
 * The term conversion proof generator.
 *
 * This class is used for proofs of t = t', where t' is obtained from t by
 * applying (context-free) small step rewrites on subterms of t. Its main
 * interface functions are:
 * (1) addRewriteStep(t,s,<justification>) which notifies this class that t
 * rewrites to s, where justification is either a proof generator or proof
 * step,
 * (2) getProofFor(f) where f is any equality that can be justified by the
 * rewrite steps given above.
 *
 * For example, say we make the following calls:
 *   addRewriteStep(a,b,P1)
 *   addRewriteStep(f(a),c,P2)
 *   addRewriteStep(c,d,P3)
 * where P1 and P2 are proof steps. Afterwards, this class may justify any
 * equality t = s where s is obtained by applying the rewrites a->b, f(a)->c,
 * c->d, based on the strategy outlined below [***]. For example, the call to:
 *   getProofFor(g(f(a),h(a),f(e)) = g(d,h(b),f(e)))
 * will return the proof:
 *   CONG(
 *     TRANS(P2,P3),     ; f(a)=d
 *     CONG(P1 :args h), ; h(a)=h(b)
 *     REFL(:args f(e))  ; f(e)=f(e)
 *   :args g)
 *
 * [***] This class traverses the left hand side of a given equality-to-prove
 * (the term g(f(a),h(a),e) in the above example) and "replays" the rewrite
 * steps to obtain its rewritten form. To do so, it applies any available
 * rewrite step both at pre-rewrite (pre-order traversal) and post-rewrite
 * (post-order traversal). It thus does not require the user of this class to
 * distinguish whether a rewrite is a pre-rewrite or a post-rewrite during
 * addRewriteStep. In particular, notice that in the above example, we realize
 * that f(a) --> c at pre-rewrite instead of post-rewriting a --> b and then
 * ending with f(a)=f(b).
 */
class TConvProofGenerator : public ProofGenerator
{
 public:
  /** Constructor
   *
   * @param pnm The proof node manager for constructing ProofNode objects.
   * @param c The context that this class depends on. If none is provided,
   * this class is context-independent.
   * @param tpol The policy for applying rewrite steps of this class. For
   * details, see d_policy.
   */
  TConvProofGenerator(ProofNodeManager* pnm,
                      context::Context* c = nullptr,
                      TConvPolicy pol = TConvPolicy::FIXPOINT);
  ~TConvProofGenerator();
  /**
   * Add rewrite step t --> s based on proof generator.
   */
  void addRewriteStep(Node t, Node s, ProofGenerator* pg);
  /** Same as above, for a single step */
  void addRewriteStep(Node t, Node s, ProofStep ps);
  /** Same as above, with explicit arguments */
  void addRewriteStep(Node t,
                      Node s,
                      PfRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args);
  /** Has rewrite step for term t */
  bool hasRewriteStep(Node t) const;
  /** 
   * Get rewrite step for term t, returns the s provided in a call to
   * addRewriteStep if one exists, or null otherwise.
   */
  Node getRewriteStep(Node t) const;
  /**
   * Get the proof for formula f. It should be the case that f is of the form
   * t = t', where t' is the result of rewriting t based on the rewrite steps
   * registered to this class.
   *
   * @param f The equality fact to get the proof for.
   * @return The proof for f.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 protected:
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /** The (lazy) context dependent proof object. */
  LazyCDProof d_proof;
  /** map to rewritten forms */
  NodeNodeMap d_rewriteMap;
  /**
   * Policy for how rewrites are applied to terms. As a simple example, say we
   * have registered the rewrite steps:
   *   addRewriteStep( a, f(c), p1 )
   *   addRewriteStep( c, d, p2 )
   * Then getProofForRewriting(f(a,c),pf) returns a proof of:
   *   f(a,c) = f(f(d),d) if d_policy is FIXPOINT,
   *   f(a,c) = f(f(c),d) if d_policy is ONCE.
   */
  TConvPolicy d_policy;
  /**
   * Adds a proof of t = t' to the proof pf where t' is the result of rewriting
   * t based on the rewrite steps registered to this class. This method then
   * returns the proved equality t = t'.
   */
  Node getProofForRewriting(Node t, LazyCDProof& pf);
  /**
   * Register rewrite step, returns the equality t=s if t is distinct from s
   * and a rewrite step has not already been registered for t.
   */
  Node registerRewriteStep(Node t, Node s);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */
