/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof annotation identifier enumeration.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ANNOTATION_ID_H
#define CVC5__PROOF__ANNOTATION_ID_H

#include "expr/node.h"

namespace cvc5::internal {

/**
 * Identifiers for annotation steps in proofs.
 */
enum class AnnotationId : uint32_t
{
  NONE,
  /** Annotation used for theory lemmas. */
  THEORY_LEMMA,
};

/**
 * Converts an annotation identifier to a string.
 *
 * @param id The annotation identifier
 * @return The name of the annotation identifier
 */
const char* toString(AnnotationId id);

/**
 * Writes an annotation identifier to a stream.
 *
 * @param out The stream to write to
 * @param id The annotation identifier to write
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, AnnotationId id);

/** Make a node from an annotation identifier. */
Node mkAnnotationId(NodeManager* nm, AnnotationId id);

/** Get an annotation identifier from a node, return false if we fail. */
bool getAnnotationId(TNode n, AnnotationId& id);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ANNOTATION_ID_H */
