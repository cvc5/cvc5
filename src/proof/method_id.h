/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Method identifier enumeration
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__METHOD_ID_H
#define CVC5__PROOF__METHOD_ID_H

#include "expr/node.h"

namespace cvc5::internal {

/**
 * Identifiers for rewriters and substitutions, which we abstractly
 * classify as "methods".  Methods have a unique identifier in the internal
 * proof calculus implemented by the checker below.
 *
 * A "rewriter" is abstractly a method from Node to Node, where the output
 * is semantically equivalent to the input. The identifiers below list
 * various methods that have this contract. This identifier is used
 * in a number of the builtin rules.
 *
 * A substitution is a method for turning a formula into a substitution.
 */
enum class MethodId : uint32_t
{
  //---------------------------- Rewriters
  // Rewriter::rewrite(n)
  RW_REWRITE,
  // d_ext_rew.extendedRewrite(n);
  RW_EXT_REWRITE,
  // Rewriter::rewriteExtEquality(n)
  RW_REWRITE_EQ_EXT,
  // Evaluator::evaluate(n)
  RW_EVALUATE,
  // identity
  RW_IDENTITY,
  // theory preRewrite, note this is only intended to be used as an argument
  // to THEORY_REWRITE in the final proof. It is not implemented in
  // Rewriter::rewriteViaMethod, see documentation in proof_rule.h for
  // THEORY_REWRITE.
  RW_REWRITE_THEORY_PRE,
  // same as above, for theory postRewrite
  RW_REWRITE_THEORY_POST,
  //---------------------------- Substitutions
  // (= x y) is interpreted as x -> y, using Node::substitute
  SB_DEFAULT,
  // P, (not P) are interpreted as P -> true, P -> false using Node::substitute
  SB_LITERAL,
  // P is interpreted as P -> true using Node::substitute
  SB_FORMULA,
  //---------------------------- Substitution applications
  // multiple substitutions are applied sequentially
  SBA_SEQUENTIAL,
  // multiple substitutions are applied simultaneously
  SBA_SIMUL,
  // multiple substitutions are applied to fix point
  SBA_FIXPOINT
  // For example, for x -> u, y -> f(z), z -> g(x), applying this substituion to
  // y gives:
  // - f(g(x)) for SBA_SEQUENTIAL
  // - f(z) for SBA_SIMUL
  // - f(g(u)) for SBA_FIXPOINT
  // Notice that SBA_FIXPOINT should provide a terminating rewrite system
  // as a substitution, or else non-termination will occur during proof
  // checking.
};
/** Converts a rewriter id to a string. */
const char* toString(MethodId id);
/** Write a rewriter id to out */
std::ostream& operator<<(std::ostream& out, MethodId id);
/** Make a method id node */
Node mkMethodId(MethodId id);

/** get a method identifier from a node, return false if we fail */
bool getMethodId(TNode n, MethodId& i);
/**
 * Get method identifiers from args starting at the given index. Store their
 * values into ids, ida, and idr. This method returns false if args does not
 * contain valid method identifiers at position index in args.
 */
bool getMethodIds(const std::vector<Node>& args,
                  MethodId& ids,
                  MethodId& ida,
                  MethodId& idr,
                  size_t index);
/**
 * Add method identifiers ids, ida and idr as nodes to args. This does not add
 * ids, ida or idr if their values are the default ones.
 */
void addMethodIds(std::vector<Node>& args,
                  MethodId ids,
                  MethodId ida,
                  MethodId idr);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__METHOD_ID_H */
