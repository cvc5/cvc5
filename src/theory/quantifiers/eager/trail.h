/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Backtracking trail objects and the trail stack of the eager E-matching core.
 *
 * Ported from Z3: src/util/trail.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * The trail objects are Z3's: undo actions, pushed when the state changes. The
 * stack is a context-dependent list of them, on a context of the core's own.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__TRAIL_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__TRAIL_H

#include <cstddef>
#include <cstdint>
#include <new>

#include "base/check.h"
#include "context/cdlist.h"
#include "context/context.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

/** An action to be undone when the enclosing scope is popped. */
class Trail
{
 public:
  virtual ~Trail() = default;
  /** Undo the action, when the scope it was pushed in is popped. */
  virtual void undo() = 0;
};

/** Restore a variable to the value it had when the trail object was created. */
template <typename T>
class ValueTrail : public Trail
{
 public:
  /** Save the current value of value. */
  ValueTrail(T& value) : d_value(value), d_oldValue(value) {}

  /** Restore the saved value. */
  void undo() override { d_value = d_oldValue; }

 private:
  /** The variable to restore. */
  T& d_value;
  /** Its value when the trail object was created. */
  T d_oldValue;
};

/** Set a pointer back to null. */
template <typename T>
class SetPtrTrail : public Trail
{
 public:
  /** Reset ptr, which is null now and is about to be set, on undo. */
  SetPtrTrail(T*& ptr) : d_ptr(ptr) { Assert(d_ptr == nullptr); }

  /** Set the pointer back to null. */
  void undo() override { d_ptr = nullptr; }

 private:
  /** The pointer to reset. */
  T*& d_ptr;
};

/** Delete a heap-allocated object. */
template <typename T>
class NewObjTrail : public Trail
{
 public:
  /** Take ownership of obj, which is deleted on undo. */
  NewObjTrail(T* obj) : d_obj(obj) {}

  /** Delete the object. */
  void undo() override { delete d_obj; }

 private:
  /** The object to delete. */
  T* d_obj;
};

/** Undo a trail object owned elsewhere; see TrailStack::pushPtr. */
class PtrTrail : public Trail
{
 public:
  /** Forward to t, which must outlive the scope. */
  PtrTrail(Trail* t) : d_trail(t) {}

  /** Undo the forwarded trail object, without destroying it. */
  void undo() override { d_trail->undo(); }

 private:
  /** The trail object owned elsewhere. */
  Trail* d_trail;
};

/** Undoes and destroys a trail object popped from a TrailStack. */
struct TrailCleanup
{
  /** Undo t and run its destructor; its memory is the context's. */
  void operator()(Trail* t)
  {
    t->undo();
    t->~Trail();
  }
};

/**
 * A stack of scopes, each holding the trail objects to undo when it is popped,
 * and the memory to release then.
 *
 * It is backed by a context of its own, which the core pushes and pops at its
 * own pace (see EagerEMatching::syncLevel), and not by the SAT context: the
 * trail objects are a context-dependent list, which undoes them when it
 * shrinks, and they and the objects of allocate() live in the context's
 * memory manager, so that pushing one costs a pointer bump.
 */
class TrailStack
{
  /** Frees a heap allocation of allocate(). */
  class FreeTrail : public Trail
  {
   public:
    /** Free mem, from ::operator new, on undo. */
    FreeTrail(void* mem) : d_mem(mem) {}

    /** Free the allocation. */
    void undo() override { ::operator delete(d_mem); }

   private:
    /** The allocation to free. */
    void* d_mem;
  };

 public:
  /** The alignment of allocate(), which is enough for the core's objects. */
  static constexpr size_t s_align = alignof(uint64_t);

  /** An empty stack, at scope level 0. */
  TrailStack() : d_trail(&d_context, true, TrailCleanup()) { d_context.push(); }

  /**
   * Undo every trail object and release all memory. The objects pushed before
   * the first pushScope are at the base scope of the context, so that this
   * can pop them too.
   */
  void reset()
  {
    d_context.popto(0);
    d_context.push();
  }

  /**
   * Allocate size bytes, aligned to s_align, which are released when the
   * current scope is popped. Destructors are not run, so only objects whose
   * destruction is a no-op (or is arranged for by a trail object) may be
   * allocated here.
   */
  void* allocate(size_t size)
  {
    // The memory manager does not align, but everything allocated from it is
    // a multiple of s_align: these objects, and the context's scopes and the
    // saved sizes of d_trail, which hold pointers.
    size = (size + s_align - 1) & ~(s_align - 1);
    if (size > context::ContextMemoryManager::getMaxAllocationSize())
    {
      void* mem = ::operator new(size);
      push(FreeTrail(mem));
      return mem;
    }
    void* mem = d_context.getCMM()->newData(size);
    Assert(reinterpret_cast<uintptr_t>(mem) % s_align == 0);
    return mem;
  }

  /**
   * Push a trail object that is not owned by the stack, such as a member of
   * its owner, which is undone but not destroyed: it is pushed through a
   * forwarder, which is destroyed instead.
   */
  void pushPtr(Trail* t) { push(PtrTrail(t)); }

  /** Copy obj into the stack's memory and push it. */
  template <typename TrailObject>
  void push(const TrailObject& obj)
  {
    static_assert(alignof(TrailObject) <= s_align);
    d_trail.push_back(new (allocate(sizeof(TrailObject))) TrailObject(obj));
  }

  /**
   * The context of the stack, for the context-dependent data that is popped
   * with it.
   */
  context::Context* getContext() { return &d_context; }

  /**
   * The number of scopes pushed by pushScope. The context's base scope holds
   * the objects pushed before the first one (see reset).
   */
  uint32_t getScopeLevel() const { return d_context.getLevel() - 1; }

  /** Push a new scope. */
  void pushScope() { d_context.push(); }

  /**
   * Pop numScopes scopes, undoing their trail objects, newest first, and
   * releasing their memory. At most getScopeLevel() scopes may be popped.
   */
  void popScope(size_t numScopes)
  {
    Assert(numScopes < d_context.getLevel());
    d_context.popto(d_context.getLevel() - static_cast<uint32_t>(numScopes));
  }

 private:
  /** The context of the stack, whose scopes are the stack's. */
  context::Context d_context;
  /** The trail objects, undone and destroyed as the context pops. */
  context::CDList<Trail*, TrailCleanup> d_trail;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

/** Placement new that allocates from a trail stack. */
inline void* operator new(
    size_t s, cvc5::internal::theory::quantifiers::eager::TrailStack& t)
{
  return t.allocate(s);
}

/** Matching delete for trail stack placement new; memory is freed in bulk. */
inline void operator delete(
    void*, cvc5::internal::theory::quantifiers::eager::TrailStack&)
{
}

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__TRAIL_H */
