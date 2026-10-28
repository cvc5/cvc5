/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.lang.ref.Cleaner;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.LongConsumer;

/**
 * Tracks the native objects that belong to one term manager and releases
 * them once their Java wrappers are no longer reachable.
 *
 * <p>There is exactly one {@code NativeContext} per native node manager. It
 * is created together with a {@link TermManager} and shared by every object
 * derived from it (solvers, terms, sorts, parsers, commands, ...). Objects
 * hold a strong reference to their context, so the context stays alive as
 * long as any of its objects does.</p>
 *
 * <p>The native library is not thread-safe with respect to a single node
 * manager: its reference counts are unsynchronized. A native object may thus
 * only be freed by the thread that is currently using its term manager, or
 * once no thread can use that term manager anymore. This class honors that
 * rule as follows:</p>
 * <ul>
 * <li>Every wrapper is tracked by a {@link Ref}, a weak reference enqueued by
 *     the garbage collector once the wrapper is unreachable. The queue is
 *     drained by {@link #register(AbstractPointer, long, LongConsumer)}, i.e.,
 *     whenever a new wrapper of the same context is created. This happens on
 *     the thread that is using the term manager at that moment, so no other
 *     thread can be using the node manager (any concurrent use would already
 *     be a data race on the native side).</li>
 * <li>Once the context itself becomes unreachable, every wrapper of it is
 *     unreachable too, and no thread can use the node manager anymore. A
 *     {@link Cleaner} then frees whatever native objects are left, including
 *     the term manager itself.</li>
 * <li>{@link AbstractPointer#deletePointer()} frees a native object
 *     immediately on the calling thread.</li>
 * </ul>
 *
 * <p>Native functions that borrow a pointer for longer than a single call
 * (e.g., the input parser, which keeps raw pointers to its solver and symbol
 * manager) are backed by strong Java references from the borrowing wrapper to
 * the borrowed wrappers, so the borrowed objects cannot be reclaimed first.
 * For all other native calls, the arguments are copied before the call can
 * re-enter Java code, and a native object is never freed in the middle of a
 * native call on the same thread unless that call re-enters Java code.</p>
 */
final class NativeContext
{
  /** Frees the remaining native objects of contexts that became unreachable. */
  private static final Cleaner CLEANER = Cleaner.create();

  /**
   * Contexts that may still own native objects, for {@link Context#deletePointers()}.
   * Weakly referenced, so that the registry does not keep contexts alive.
   */
  private static final Set<NativeContext> LIVE =
      Collections.newSetFromMap(new WeakHashMap<NativeContext, Boolean>());

  /** Number of contexts reclaimed by the cleaner, see {@link #releasedContexts()}. */
  private static final AtomicLong RELEASED_CONTEXTS = new AtomicLong();

  /**
   * Tracks one native object.
   *
   * <p>The referent is the Java wrapper; the native pointer and the function
   * that frees it are stored here so that the native object can be freed
   * after the wrapper has been collected.</p>
   */
  static final class Ref extends WeakReference<AbstractPointer>
  {
    private final Registry registry;
    private final LongConsumer deleter;
    private long pointer;
    private Ref prev;
    private Ref next;

    private Ref(AbstractPointer wrapper, long pointer, LongConsumer deleter, Registry registry)
    {
      super(wrapper, registry.queue);
      this.registry = registry;
      this.pointer = pointer;
      this.deleter = deleter;
    }

    /**
     * Free the native object, if not already freed.
     *
     * @return true if the native object was freed by this call.
     */
    boolean release()
    {
      long p;
      synchronized (this)
      {
        p = pointer;
        pointer = 0;
      }
      if (p == 0)
      {
        return false;
      }
      registry.unlink(this);
      deleter.accept(p);
      registry.freed++;
      return true;
    }
  }

  /**
   * The state shared between a context and the cleaner action that runs
   * once the context is unreachable. It must not reference the context.
   */
  private static final class Registry implements Runnable
  {
    /** Refs whose wrappers have been collected. */
    private final ReferenceQueue<AbstractPointer> queue = new ReferenceQueue<>();
    /** Doubly-linked list of tracked refs, most recently registered first. */
    private Ref head;
    /** Number of native objects freed so far, see {@link #freedObjects(AbstractPointer)}. */
    private long freed;

    Ref register(AbstractPointer wrapper, long pointer, LongConsumer deleter)
    {
      reap();
      Ref ref = new Ref(wrapper, pointer, deleter, this);
      synchronized (this)
      {
        ref.next = head;
        if (head != null)
        {
          head.prev = ref;
        }
        head = ref;
      }
      return ref;
    }

    /** Free the native objects of all wrappers collected so far. */
    void reap()
    {
      Ref ref;
      while ((ref = (Ref) queue.poll()) != null)
      {
        ref.release();
      }
    }

    synchronized void unlink(Ref ref)
    {
      if (ref.prev != null)
      {
        ref.prev.next = ref.next;
      }
      else if (head == ref)
      {
        head = ref.next;
      }
      else
      {
        return; // already unlinked
      }
      if (ref.next != null)
      {
        ref.next.prev = ref.prev;
      }
      ref.prev = null;
      ref.next = null;
    }

    /**
     * Free every native object of this registry, in reverse order of
     * registration. Wrappers that are still reachable are left with a null
     * pointer.
     */
    void releaseAll()
    {
      List<Ref> refs = new ArrayList<>();
      synchronized (this)
      {
        for (Ref ref = head; ref != null; ref = ref.next)
        {
          refs.add(ref);
        }
      }
      for (Ref ref : refs)
      {
        AbstractPointer wrapper = ref.get();
        if (wrapper != null)
        {
          wrapper.pointer = 0;
        }
        ref.release();
      }
    }

    /** Cleaner action, invoked once the owning context is unreachable. */
    @Override
    public void run()
    {
      releaseAll();
      RELEASED_CONTEXTS.incrementAndGet();
    }
  }

  private final Registry registry = new Registry();

  /** Create the context of a new term manager. */
  NativeContext()
  {
    CLEANER.register(this, registry);
    synchronized (LIVE)
    {
      LIVE.add(this);
    }
  }

  /**
   * Track a native object.
   *
   * <p>Must be called on the thread that is using this context's term manager:
   * it also frees the native objects of previously collected wrappers.</p>
   *
   * @param wrapper The Java wrapper of the native object.
   * @param pointer The native pointer.
   * @param deleter The function that frees the native object.
   * @return The ref tracking the native object.
   */
  Ref register(AbstractPointer wrapper, long pointer, LongConsumer deleter)
  {
    return registry.register(wrapper, pointer, deleter);
  }

  /**
   * The number of native objects freed so far in the context of the given
   * object. For tests.
   */
  static long freedObjects(AbstractPointer object)
  {
    return object.ctx.registry.freed;
  }

  /**
   * The number of contexts that have been reclaimed after becoming
   * unreachable. For tests.
   */
  static long releasedContexts()
  {
    return RELEASED_CONTEXTS.get();
  }

  /**
   * Free every native object of every context, see {@link Context#deletePointers()}.
   */
  static void releaseAll()
  {
    List<NativeContext> contexts;
    synchronized (LIVE)
    {
      contexts = new ArrayList<>(LIVE);
    }
    for (NativeContext context : contexts)
    {
      context.registry.releaseAll();
    }
  }
}
