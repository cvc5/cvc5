/*********************                                                        */
/*! \file justify_stack.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification stack
 **/

#include "cvc4_private.h"

#ifndef CVC5__DECISION__JUSTIFY_STACK_H
#define CVC5__DECISION__JUSTIFY_STACK_H

#include "context/cdlist.h"
#include "context/cdo.h"
#include "decision/justify_info.h"
#include "expr/node.h"

namespace cvc5 {

class JustifyStack
{
 public:
  JustifyStack(context::Context* c);
  ~JustifyStack();
  /** reset the stack */
  void reset(TNode curr);
  /** clear */
  void clear();
  /** size */
  size_t size() const;
  /** Get the current assertion */
  TNode getCurrentAssertion() const;
  /** Has current assertion */
  bool hasCurrentAssertion() const;
  /** Get current justify info */
  JustifyInfo* getCurrent();
  /** Push to stack */
  void pushToStack(TNode n, prop::SatValue desiredVal);
  /** Pop from stack */
  void popStack();

 private:
  /**
   * Get or allocate justify info at position i. This does not impact
   * d_stackSizeValid.
   */
  JustifyInfo* getOrAllocJustifyInfo(size_t i);
  /** The context */
  context::Context* d_context;
  /** The current assertion we are trying to satisfy */
  context::CDO<TNode> d_current;
  /** Stack of justify info, valid up to index d_stackSizeValid-1 */
  context::CDList<std::shared_ptr<JustifyInfo> > d_stack;
  /** Current number of entries in the stack that are valid */
  context::CDO<size_t> d_stackSizeValid;
};

}  // namespace cvc5

#endif /* CVC5__DECISION__JUSTIFY_INFO_H */
