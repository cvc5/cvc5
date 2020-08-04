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
 ** \brief Term context
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__TERM_CONTEXT_H
#define CVC4__EXPR__TERM_CONTEXT_H

#include "expr/node.h"

namespace CVC4 {

/**
 * This is an abstract class for computing "term context identifiers". A term
 * context identifier is a hash value that identifies some property of the
 * context in which a term occurs.
 */
class TermContext
{
public:
  TermContext(uint32_t ivalue = 0);
  virtual ~TermContext(){}
  /** Initial value */
  uint32_t initialValue();
  /** 
   * Compute the term context identifier of the index^th child of t, where tval
   * is the term context identifier of t.
   */
  virtual uint32_t computeValue(TNode t, uint32_t tval, size_t index) = 0;
private:
  /** The initial value for terms in no context */
  uint32_t d_initVal;
};

/**
 * Computes whether we are inside a term (as opposed to being part of Boolean
 * skeleton) and whether we are inside a quantifier.
 */
class RtfTermContext : public TermContext
{
public:
  RtfTermContext();
  /** Compute the value */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) override;
  /** get value */
  static uint32_t getValue(bool inQuant, bool inTerm);
  /** get flags */
  static void getFlags(uint32_t val, bool& inQuant, bool& inTerm);
private:
  /** 
   * Returns true if the children of t should be considered in a "term" context.
   */
  static bool hasNestedTermChildren( TNode t );
};

// TODO: polarity context
#if 0
/**
 * Computes the polarity of a term.
 */
class PolarityTermContext : public TermContext
{
public:
  PolarityTermContext();
  /** Compute the value */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) override;
  /** get value */
  static uint32_t getValue(bool hasPol, bool pol);
  /** get flags */
  static void getFlags(uint32_t val, bool& hasPol, bool& pol);
};
#endif


/** 
 * A (term-context) sensitive term. This is a wrapper around a Node that
 * additionally has a term context identifier, see getTermContext(). It depends
 * on a pointer to a TermContext callback class from above.
 */
class TCtxNode
{
public:
  TCtxNode(Node n, const TermContext * tctx);
  /** get number of children */
  size_t getNumChildren() const;
  /** get child at index i */
  TCtxNode getChild(size_t i) const;
  /** get node */
  Node getNode() const;
  /** get term context */
  uint32_t getTermContext() const;
  //---------------------- utility methods
  /** 
   * Get node hash, which is a unique node representation of this TCtxNode.
   * This method calls the method below on the data members of this class.
   */
  Node getNodeHash() const;
  /** 
   * Get node hash, which is a unique node representation of the pair (n, val).
   */
  static Node computeNodeHash(Node n, uint32_t val);
  /** 
   * Decompose node hash, which is an inverse of the above operation.
   */
  static Node decomposeNodeHash(Node h, uint32_t& val);
  //---------------------- end utility methods
private:
  /** private constructor */
  TCtxNode(Node n, uint32_t val, const TermContext * tctx);
  /** The node */
  Node d_node;
  /** The term context identifier */
  uint32_t d_val;
  /** The term context */
  const TermContext * d_tctx;
};

class TCtxStack
{
public:
  TCtxStack(const TermContext * tctx);
  virtual ~TCtxStack(){}
  /** Push t to the stack */
  void pushInitial(Node t);
  /** Push all children of t to the stack */
  virtual void pushChildren(Node t, uint32_t tval);
  /** Push the child of t with the given index to the stack */
  virtual void pushChild(Node t, uint32_t tval, size_t index);
  /** Push t to the stack */
  void push(Node t, uint32_t tval);
  /** Pop a term from the context */
  void pop();
  /** Clear the stack */
  void clear();
  /** Return the size of the stack */
  size_t size();
  /** Return true if the stack is empty */
  bool empty() const;
  /** Get the current stack element */
  std::pair<Node, uint32_t> getCurrent() const;
private:
  /** The stack */
  std::vector<std::pair<Node, uint32_t>> d_stack;
  /** The term context */
  const TermContext * d_tctx;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */
