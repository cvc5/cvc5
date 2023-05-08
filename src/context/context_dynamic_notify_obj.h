/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Dynamic notify object.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__CONTEXT__CONTEXT_DYNAMIC_NOTIFY_OBJ_H
#define CVC5__CONTEXT__CONTEXT_DYNAMIC_NOTIFY_OBJ_H

#include "context/context.h"

namespace cvc5::context {

/**
 * An object that is called to restore its state when dynamically marked to do
 * so. In particular its main methods are markNeedsRestore and notifyRestore.
 * When markNeedsRestore is called in the current context, the latter
 * method is called when backtracking to that context level.
 */
class ContextDynamicNotifyObj
{
 public:
  /**
   */
  ContextDynamicNotifyObj(Context* c);
  /** Destructor */
  virtual ~ContextDynamicNotifyObj();

 protected:
  /**
   * The notification class, which is a context object which notifies the
   * parent of when to restore.
   */
  class CallbackContextObj : public ContextObj
  {
   public:
    CallbackContextObj(Context* c, ContextDynamicNotifyObj* cdno);
    virtual ~CallbackContextObj();
    void markNeedsRestore();

   protected:
    /** Save does nothing */
    ContextObj* save(ContextMemoryManager* pCMM) override;
    /** Restore notifies the parent */
    void restore(ContextObj* pContextObjRestore) override;
    /** To notify */
    ContextDynamicNotifyObj* d_cdno;

   private:
    /**
     * Copy constructor - it's private to ensure it is only used by save().
     * Basic CDO objects, cannot be copied-they have to be unique.
     */
    CallbackContextObj(CallbackContextObj& cco);
  };
  /** Instance of the above class */
  CallbackContextObj d_cn;
  /**
   * This is the method called to notify the object of a pop.  It must be
   * implemented by the subclass. It is protected since context is out
   * friend.
   */
  virtual void notifyRestore() = 0;
  /** Mark needs notify */
  void markNeedsRestore();
};

}  // namespace cvc5::context

#endif /* CVC5__CONTEXT__CONTEXT_DYNAMIC_NOTIFY_OBJ_H */
