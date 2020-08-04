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

class TermContext
{
public:
  TermContext(int32_t dvalue = 0);
  /** Push t to the stack */
  void pushInitial(Node t);
  /** Push all children of t to the stack */
  virtual void pushChildren(Node t, int32_t tval);
  /** Push the child of t with the given index to the stack */
  virtual void pushChild(Node t, int32_t tval, size_t index);
  /** Push t to the stack */
  void push(Node t, int32_t tval);
  /** Pop a term from the context */
  void pop();
  /** Clear the stack */
  void clear();
  /** Return the size of the stack */
  size_t size();
  /** Return true if the stack is empty */
  bool empty() const;
  /** Get the current stack element */
  std::pair<Node, int32_t> getCurrent() const;
private:
  /** 
   * Compute the term context value of the index^th child of t, where tval
   * is the term context value of t.
   */
  virtual int32_t computePushValue(Node t, int32_t tval, size_t child) = 0;
  /** The default value when no stack */
  int32_t d_defaultVal;
  /** The stack */
  std::vector<std::pair<Node, int32_t>> d_stack;
};

/**
 * Computes whether we are inside a term (as opposed to being part of Boolean
 * skeleton) and whether we are inside a quantifier.
 */
class RtfTermContext : public TermContext
{
public:
  RtfTermContext();
  /** Are we under a quantifier? */
  bool inQuant() const;
  /** Are we in a term? */
  bool inTerm() const;
  /** get value */
  static int32_t getValue(bool inQuant, bool inTerm);
  /** get flags */
  static void getFlags(int32_t val, bool& inQuant, bool& inTerm);
private:
  /** Compute the push value */
  int32_t computePushValue(TNode t, int32_t tval, size_t child);
  /** has nested term children */
  static bool hasNestedTermChildren( TNode t );
};

// TODO: polarity context

}  // namespace CVC4

#endif /* CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */
