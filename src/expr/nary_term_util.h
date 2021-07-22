/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * N-ary term utilities
 */

#include "cvc5_private.h"

#ifndef CVC4__EXPR__NARY_TERM_UTIL__H
#define CVC4__EXPR__NARY_TERM_UTIL__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace expr {

/** Mark variable as list */
void markListVar(TNode fv);
/** Is list variable */
bool isListVar(TNode fv);

/** Contains list variable */
bool hasListVar(TNode n);

/**
 * Compute list variable context
 * Get the parent kind of each list variable in n, or fail if a list
 * variable occurs in two contexts.
 */
bool getListVarContext(TNode n, std::map<Node, Kind>& context);

/** get the null terminator */
Node getNullTerminator(Kind k, TypeNode tn);

/**
 * Substitution with list semantics.
 * Handles mixtures of list / non-list variables in vars.
 * List variables are mapped to SEXPR whose children are the list to substitute.
 */
Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs);

}  // namespace expr
}  // namespace cvc5

#endif /* CVC4__EXPR__NARY_TERM_UTIL__H */
