/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strings proof utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__PROOF_H
#define CVC4__THEORY__STRINGS__PROOF_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "util/safe_print.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** Types of proof steps used in the procedure
 */
enum class ProofStep : uint32_t
{
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion P:F
  ASSUME,
  // ======== Substitution
  // Children: (P:(= x1 t1), ..., P:(= xn tn))
  // Arguments: (t)
  // ---------------------------------------------------------------
  // Conclusion: P:(= t t.substitute(x1,t1). ... .substitute(xn,tn))
  SUBS,
  // ======== Rewrite
  // Children: none
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: P:(= t Rewriter::rewrite(t))
  REWRITE,
  // ======== Reflexive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: P:(= t t)
  REFL,
  // ======== Symmetric
  // Children: (P:(= t1 t2))
  // Arguments: none
  // -----------------------
  // Conclusion: P:(= t2 t1)
  SYMM,
  // ======== Transitivity
  // Children: (P:(= t1 t2), ..., P:(= t{n-1} tn))
  // Arguments: none
  // -----------------------
  // Conclusion: P:(= t1 tn)
  TRANS,
  // ======== Normal form unify
  // Children: (P:(= (str.++ r t1 t2) (str.++ r s1 s2)),
  //            P:(= (str.len s1) (str.len s2)))
  // Arguments: none
  // ---------------------
  // Conclusion: (= t1 s1)
  N_UNIFY,
  // ======== Normal form unify reverse
  // Children: (P:(= (str.++ t2 t1 r) (str.++ s2 s1 r)),
  //            P:(= (str.len s1) (str.len s2)))
  // Arguments: none
  // ---------------------
  // Conclusion: (= t1 s1)
  N_UNIFY_REV,

  // ======== Congruence  (subsumed by Substitute?)
  // Children: (P:(= t1 s1), ..., P:(= tn sn))
  // Arguments: (f)
  // ---------------------------------------------
  // Conclusion: P:(= (f t1 ... tn) (f s1 ... sn))
  // CONG,

  // Unknown
  UNKNOWN,
};

/**
 * Converts an proof step to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The proof step
 * @return The name of the proof step
 */
const char* toString(ProofStep id);

/**
 * Writes an proof step name to a stream.
 *
 * @param out The stream to write to
 * @param id The proof step to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, ProofStep id);

class ProofManager;

/** A node in a strings proof */
class ProofNode
{
  friend class ProofManager;

 public:
  ProofNode(ProofStep id,
            const std::vector<std::shared_ptr<ProofNode>>& children,
            const std::vector<Node>& args);
  ~ProofNode() {}
  /** get id */
  ProofStep getId() const;
  /** get what this node proves, or the null node if this is an invalid proof */
  Node getResult() const;
  /** print debug */
  void printDebug(std::ostream& os) const;

  /** apply substitution */
  static Node applySubstitution(Node n, const std::vector<Node>& exp);

 private:
  /** The proof step */
  ProofStep d_id;
  /** The children of this node */
  std::vector<std::shared_ptr<ProofNode>> d_children;
  /** arguments of this node */
  std::vector<Node> d_args;
  /** The fact that has been proven */
  Node d_proven;
  /** compute what has been proven, return true if proof is valid */
  bool initialize(ProofStep id,
                  const std::vector<std::shared_ptr<ProofNode>>& children,
                  const std::vector<Node>& args);
  /** invalidate */
  void invalidate();
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_H */
