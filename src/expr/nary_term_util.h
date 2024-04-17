/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * N-ary term utilities
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__NARY_TERM_UTIL__H
#define CVC5__EXPR__NARY_TERM_UTIL__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace expr {

/** Mark variable as list */
void markListVar(TNode fv);
/** Is list variable */
bool isListVar(TNode fv);

/** Contains list variable */
bool hasListVar(TNode n);

/**
 * Compute list variable context
 * Stores (one of the) parents for each list variable in n, or fail if a list
 * variable occurs beneath parents that have different kinds.
 */
bool getListVarContext(TNode n, std::map<Node, Node>& context);

/**
 * Get the null terminator for kind k and type node tn.
 *
 * Examples of null terminators:
 *   false for (OR, bool)
 *   true for (AND, bool)
 *   (as seq.empty (Seq Int)) for (STRING_CONCAT, (Seq Int)
 *   #x0 for (BITVECTOR_OR, (_ BitVec 4))
 */
Node getNullTerminator(Kind k, TypeNode tn);

/**
 * Substitution with list semantics.
 * Handles mixtures of list / non-list variables in vars.
 * List variables are mapped to SEXPR whose children are the list to substitute.
 *
 * @param src The term to substitute
 * @param vars The domain of the substitution
 * @param subs The range of the substitution
 * @return the substituted term.
 */
Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs);
/**
 * Same as above, with visited cache.
 *
 * @param src The term to substitute
 * @param vars The domain of the substitution
 * @param subs The range of the substitution
 * @return the substituted term.
 */
Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    std::unordered_map<TNode, Node>& visited);

/**
 * @param k A kind
 * @return true if k is associative, commutative and idempotent.
 */
bool isAssocCommIdem(Kind k);
/**
 * @param k A kind
 * @return true if k is associative.
 */
bool isAssoc(Kind k);
/**
 * Get the normal form of a that takes into account associativity,
 * commutativity, and idempotency if applicable.
 * This is used by ProofRule::NORM.
 *
 * @param a The term.
 * @return its normal form.
 */
Node getACINormalForm(Node a);
/**
 * Return true if a and b can be shown equivalent by computing normal forms as
 * above.
 *
 * @param a The first term
 * @param b The second term
 * @return true if a and b were successfully shown to be equal.
 */
bool isACINorm(Node a, Node b);

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__NARY_TERM_UTIL__H */
