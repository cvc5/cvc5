/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Context class and context manager.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__CONTEXT__CONTEXT_DYNAMIC_NOTIFY_OBJ_H
#define CVC5__CONTEXT__CONTEXT_DYNAMIC_NOTIFY_OBJ_H

#include "context/context.h"

namespace cvc5::context {

/**
 */
class ContextDynamicNotifyObj
{
public:

  /**
   */
  ContextDynamicNotifyObj(Context* c) : d_cn(c, this) {}

  /**
   */
  virtual ~ContextDynamicNotifyObj();

 protected:
   /**
    * The notification class, which is a context object which notifies the
    * parent of when to restore.
    */
   class CallbackContextObj : public ContextObj
   {
   public:
     CallbackContextObj(Context* c, ContextDynamicNotifyObj* cdno) : ContextObj(c), d_cdno(cdno) {}
     virtual ~CallbackContextObj(){}
     void markNeedsRestore() { makeCurrent(); }
   protected:
     /** Save does nothing */
     ContextObj* save(ContextMemoryManager* pCMM) override { return this; }
     /** Restore notifies the parent */
     void restore(ContextObj* pContextObjRestore) override { d_cdno->notifyRestore(); }
     /** To notify */
     ContextDynamicNotifyObj* d_cdno;
   };
   CallbackContextObj d_cn;
  /**
   * This is the method called to notify the object of a pop.  It must be
   * implemented by the subclass. It is protected since context is out
   * friend.
   */
  virtual void notifyRestore() = 0;
  /** Mark needs notify */
  void markNeedsRestore()
  {
    d_cn.markNeedsRestore();
  }
};


}  // namespace cvc5::context

#endif /* CVC5__CONTEXT__CONTEXT_DYNAMIC_NOTIFY_OBJ_H */
