/*********************                                                        */
/*! \file infer_info.h
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

#ifndef CVC4__THEORY__STRINGS__STRING_PROOF_H
#define CVC4__THEORY__STRINGS__STRING_PROOF_H

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
  // Assumption (a leaf)
  // Children: none
  // Arguments: (P)
  ASSUME,
  // Substitution
  // Children: (P:(x1=t1), ..., P:(xn=tn))
  // Arguments: (t)
  // x1 = t1 ^ ... ^ x = tn
  // ------------------------------
  // t = ( t { x1 -> t1, ..., xn -> tn } )
  SUBSTITUTE,
  // Rewrite
  // Children: none
  // Arguments: (t)
  // t
  // ---------------------
  // t = Rewriter::rewrite( t )
  REWRITE,
  // Reflexive
  // Children: none
  // Arguments: (t)
  // .
  // ----------
  // t = t
  REFL,
  // Symmetric
  // Children: (P:(t1=t2))
  // Arguments: none
  // t1 = t2
  // ----------
  // t2 = t1
  SYMM,
  // Transitivity
  // Children: (P:(t1=t2), ..., P:(t{n-1}=tn))
  // Arguments: none
  // t1 = t2 ^ ... ^ t{n-1} = tn
  // ---------------------------
  // t1 = tn
  TRANS,
  // Congruence
  // Children: (P:(t1=t2), ..., P:(t{n-1}=tn))
  // Arguments: (f)
  // t1 = t2 ^ ... ^ t{n-1} = tn
  // ---------------------------
  // f(t1) = f(tn)
  CONG,
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
  ~ProofNode() {}
  /** compute what has been proven */
  Node computeResult();
  /** print debug */
  void printDebug(std::ostream& os) const;

 private:
  ProofNode(ProofStep id,
            const std::vector<ProofNode*>& children,
            const std::vector<Node>& args);
  /** The proof step */
  ProofStep d_id;
  /** The children of this node */
  std::vector<ProofNode*> d_children;
  /** arguments of this node */
  std::vector<Node> d_args;
  /** The fact that has been proven */
  Node d_proven;
};

/**
 * A proof manager for strings
 */
class ProofManager
{
 public:
  ProofManager() {}
  ~ProofManager() {}
  /** Get proof for fact, or nullptr if it does not exist */
  ProofNode* getProof(Node fact) const;
  /** Register step
   *
   * @param fact The intended conclusion of this proof step.
   * @param id The identifier for the proof step.
   * @param children The antecendant of the proof step. Each children[i] should
   * be a fact previously registered as conclusions of a registerStep call.
   * @param args The arguments of the proof step.
   *
   * This returns true if indeed the proof step proves fact. This can fail
   * if the proof has a different conclusion than fact, or if one of the
   * children does not have a proof.
   */
  bool registerStep(Node fact,
                    ProofStep id,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args);

 private:
  /** The nodes of the proof */
  std::map<Node, std::unique_ptr<ProofNode> > d_nodes;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRING_PROOF_H */
