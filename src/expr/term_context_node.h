/*********************                                                        */
/*! \file term_context.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term context node utility.
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__TERM_CONTEXT_NODE_H
#define CVC4__EXPR__TERM_CONTEXT_NODE_H

#include "expr/node.h"
#include "expr/term_context.h"

namespace CVC4 {

/**
 * Kinds of term-context-sensitive nodes. This enumeration is based on the
 * set of information that the term is sensitive to.
 */
enum class TCtxKind : uint32_t
{
  // Remove term formula (RtfTermContext): the term is sensitive to whether
  // it appears in a term/formula context and/or beneath quantifiers.
  RTF,
  // Polarity (PolarityContext): the term is sensitive to what polarity it
  // appears in with respect to some root, either true, false or none.
  POLARITY,
  // Extended polarity (ExtendedPolarityContext): the term is sensitive to what
  // polarity it appears in with respect to some root (true, false or
  // none), as well as "entailed polarity" (true, false, or none).
  EXTENDED_POLARITY
};

/**
 * Converts a term context kind to a string. Note: This function is also used
 * in `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The term context kind
 * @return The name of the proof rule
 */
const char* toString(TCtxKind id);

/**
 * Writes a term context kind to a stream.
 *
 * @param out The stream to write to
 * @param id The term context kind  to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, TCtxKind id);

class TermContext;
class TCtxStack;

/**
 * A (term-context) sensitive term. This is a wrapper around a Node that
 * additionally has a term context identifier, see getTermContext(). It depends
 * on a pointer to a TermContext callback class from above.
 */
class TCtxNode
{
  friend class TCtxStack;

 public:
  TCtxNode(Node n, const TermContext* tctx);
  /** get number of children */
  size_t getNumChildren() const;
  /** get child at index i */
  TCtxNode getChild(size_t i) const;
  /** get node */
  Node getNode() const;
  /** get context */
  uint32_t getContextId() const;
  /** get term context */
  const TermContext* getTermContext() const;
  //---------------------- utility methods
  /**
   * Get node hash, which is a unique node representation of this TCtxNode.
   * This method calls the method below on the data members of this class.
   */
  Node getNodeHash() const;
  /**
   * Get node hash, which is a unique node representation of the pair (n, val).
   * In particular, this returns (SEXPR n (CONST_RATIONAL val)).
   */
  static Node computeNodeHash(Node n, uint32_t val);
  /**
   * Decompose node hash, which is an inverse of the above operation.
   */
  static Node decomposeNodeHash(Node h, uint32_t& val);
  //---------------------- end utility methods
 private:
  /** private constructor */
  TCtxNode(Node n, uint32_t val, const TermContext* tctx);
  /** The node */
  Node d_node;
  /** The term context identifier */
  uint32_t d_val;
  /** The term context */
  const TermContext* d_tctx;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */
