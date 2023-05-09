/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term context.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__TERM_CONTEXT_STACK_H
#define CVC5__EXPR__TERM_CONTEXT_STACK_H

#include "expr/term_context_node.h"

namespace cvc5::internal {

/**
 * A stack for term-context-sensitive terms. Its main advantage is that
 * it does not rely on explicit construction of TCtxNode for efficiency.
 */
class TCtxStack
{
 public:
  TCtxStack(const TermContext* tctx);
  virtual ~TCtxStack() {}
  /** Push t to the stack */
  void pushInitial(Node t);
  /**
   * Push all children of t to the stack, where tval is the term context hash
   * of t. */
  void pushChildren(Node t, uint32_t tval);
  /**
   * Push the child of t with the given index to the stack, where tval is
   * the term context hash of t.
   */
  void pushChild(Node t, uint32_t tval, size_t index);
  /**
   * Push the operator of t to the stack, where tval is the term context has
   * of t.
   */
  void pushOp(Node t, uint32_t tval);
  /** Push t to the stack with term context hash tval. */
  void push(Node t, uint32_t tval);
  /** Pop a term from the context */
  void pop();
  /** Clear the stack */
  void clear();
  /** Return the size of the stack */
  size_t size() const;
  /** Return true if the stack is empty */
  bool empty() const;
  /** Get the current stack element */
  std::pair<Node, uint32_t> getCurrent() const;
  /** Get the current stack element, node version */
  TCtxNode getCurrentNode() const;

 private:
  /** The stack */
  std::vector<std::pair<Node, uint32_t>> d_stack;
  /** The term context */
  const TermContext* d_tctx;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__TERM_CONTEXT_STACK_H */
