/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for proof annotation identifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ANNOTATION_ID_H
#define CVC5__PROOF__ANNOTATION_ID_H

#include <cvc5/cvc5_proof_rule.h>

#include "expr/node.h"

namespace cvc5::internal {

/** Make a node from an annotation identifier. */
Node mkAnnotationId(NodeManager* nm, AnnotationId id);

/** Get an annotation identifier from a node, return false if we fail. */
bool getAnnotationId(TNode n, AnnotationId& id);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ANNOTATION_ID_H */
