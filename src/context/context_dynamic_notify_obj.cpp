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
#include "context/context_dynamic_notify_obj.h"

namespace cvc5::context {

ContextDynamicNotifyObj::ContextDynamicNotifyObj(Context* c) : d_cn(c, this) {}
ContextDynamicNotifyObj::~ContextDynamicNotifyObj() {
  // we no longer wish to be notified
  d_cn.d_cdno = nullptr;
}

ContextDynamicNotifyObj::CallbackContextObj::CallbackContextObj(
    Context* c, ContextDynamicNotifyObj* cdno)
    : ContextObj(c), d_cdno(cdno)
{
}
ContextDynamicNotifyObj::CallbackContextObj::~CallbackContextObj()
{
  destroy();
}
void ContextDynamicNotifyObj::CallbackContextObj::markNeedsRestore()
{
  makeCurrent();
}
ContextObj* ContextDynamicNotifyObj::CallbackContextObj::save(
    ContextMemoryManager* pCMM)
{
  return new (pCMM) CallbackContextObj(*this);
}
void ContextDynamicNotifyObj::CallbackContextObj::restore(
    ContextObj* pContextObjRestore)
{
  if (d_cdno)
  {
    d_cdno->notifyRestore();
  }
}
ContextDynamicNotifyObj::CallbackContextObj::CallbackContextObj(
    CallbackContextObj& cco)
    : ContextObj(cco), d_cdno(cco.d_cdno)
{
}

void ContextDynamicNotifyObj::markNeedsRestore() { d_cn.markNeedsRestore(); }

}  // namespace cvc5::context
