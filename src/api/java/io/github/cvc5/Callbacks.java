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

import static java.lang.foreign.ValueLayout.ADDRESS;
import static java.lang.foreign.ValueLayout.JAVA_LONG;

import io.github.cvc5.capi.CApi;
import io.github.cvc5.capi.Cvc5Plugin;
import io.github.cvc5.capi.cvc5_declare_oracle_fun$fun;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.lang.ref.WeakReference;

/**
 * Upcalls from the cvc5 C API into Java: oracles and plugins.
 *
 * <p>The C API calls a callback through a function pointer, an upcall stub
 * allocated with the classes that jextract generates for the function pointer
 * types. A stub keeps its target alive like a global reference, so a stub that
 * referenced a plugin would keep the plugin, its term manager, and thus every
 * object of that term manager reachable forever. The stubs therefore only
 * reference their callback object weakly, and the {@link Solver} keeps the
 * callback objects (and with them, the stubs) alive for as long as it exists.
 * Callbacks only happen while the solver is in use. For the same reason, a
 * stub must not reference memory of its own arena, which would keep the arena
 * alive.</p>
 *
 * <p>An exception that escapes an upcall terminates the JVM. The stubs thus
 * catch every exception and report it to the C API via
 * {@code cvc5_set_callback_error()}, which aborts the operation that invoked
 * the callback. The resulting {@link CVC5ApiException} has the exception of
 * the callback as its cause.</p>
 */
final class Callbacks
{
  private Callbacks() {}

  /** The exception of the most recent failed callback on this thread. */
  private static final ThreadLocal<Failure> FAILURE = new ThreadLocal<>();

  /** A failed callback: its message and exception. */
  private static final class Failure
  {
    final String message;
    final Throwable cause;

    Failure(String message, Throwable cause)
    {
      this.message = message;
      this.cause = cause;
    }
  }

  /**
   * Report that a callback failed.
   *
   * @param what A description of the callback.
   * @param e The exception thrown by the callback.
   */
  private static void fail(String what, Throwable e)
  {
    String message = what + ": " + e;
    FAILURE.set(new Failure(message, e));
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_set_callback_error(arena.allocateFrom(message));
    }
  }

  /**
   * Attach the exception of the failed callback that caused the given error,
   * if any.
   *
   * @param error The error raised by a C API call.
   * @param message The message of the error.
   * @return The error.
   */
  static <T extends Throwable> T withCause(T error, String message)
  {
    Failure failure = FAILURE.get();
    if (failure != null)
    {
      FAILURE.remove();
      if (message.contains(failure.message) && error.getCause() == null)
      {
        error.initCause(failure.cause);
      }
    }
    return error;
  }

  /* .................................................................... */
  /* Oracles                                                              */
  /* .................................................................... */

  /** The native function of an oracle, see {@code cvc5_declare_oracle_fun()}. */
  static final class Oracle
  {
    private final NativeContext ctx;
    private final IOracle oracle;
    /** Owns the upcall stub, see {@link Callbacks}. */
    private final Arena arena = Arena.ofAuto();
    /** The upcall stub. */
    final MemorySegment function;

    Oracle(NativeContext ctx, IOracle oracle)
    {
      this.ctx = ctx;
      this.oracle = oracle;
      WeakReference<Oracle> self = new WeakReference<>(this);
      function = cvc5_declare_oracle_fun$fun.allocate(
          (size, args, state) -> applyOracle(self, size, args), arena);
    }
  }

  /**
   * {@code Cvc5Term (*fun)(size_t size, const Cvc5Term* args, void* state)}
   */
  private static MemorySegment applyOracle(WeakReference<Oracle> ref, long size, MemorySegment args)
  {
    try
    {
      Oracle oracle = ref.get();
      if (oracle == null)
      {
        throw new IllegalStateException("The oracle has been reclaimed");
      }
      // The C API transfers a reference to each argument to the callee.
      Term[] terms = Utils.getTerms(oracle.ctx, Native.handles(args, size));
      Term result = oracle.oracle.apply(terms);
      if (result == null)
      {
        throw new NullPointerException("The oracle returned null");
      }
      // The result is copied by native code before any further Java code
      // runs on this thread, so its wrapper cannot be reclaimed first.
      return result.handle();
    }
    catch (Throwable e)
    {
      fail("The oracle threw an exception", e);
      return MemorySegment.NULL;
    }
  }

  /* .................................................................... */
  /* Plugins                                                              */
  /* .................................................................... */

  /** The native plugin of an {@link AbstractPlugin}, see {@code Cvc5Plugin}. */
  static final class Plugin
  {
    private final AbstractPlugin plugin;
    /** Owns the upcall stubs and the native data, see {@link Callbacks}. */
    private final Arena arena = Arena.ofAuto();
    /** The buffer for the lemmas returned by {@code check()}. */
    private MemorySegment lemmas = MemorySegment.NULL;
    /** The {@code Cvc5Plugin} struct. */
    final MemorySegment struct;

    Plugin(AbstractPlugin plugin)
    {
      this.plugin = plugin;
      WeakReference<Plugin> self = new WeakReference<>(this);
      // The stub of get_name() captures the address of the name rather than
      // its segment, which would keep the arena alive.
      long name = arena.allocateFrom(plugin.getName()).address();
      // The states are NULL: the stubs are bound to this plugin.
      struct = Cvc5Plugin.allocate(arena);
      Cvc5Plugin.check(
          struct, Cvc5Plugin.check.allocate((size, state) -> check(self, size), arena));
      Cvc5Plugin.notify_sat_clause(struct,
          Cvc5Plugin.notify_sat_clause.allocate(
              (clause, state) -> notifySatClause(self, clause), arena));
      Cvc5Plugin.notify_theory_lemma(struct,
          Cvc5Plugin.notify_theory_lemma.allocate(
              (lemma, state) -> notifyTheoryLemma(self, lemma), arena));
      Cvc5Plugin.get_name(
          struct, Cvc5Plugin.get_name.allocate(() -> MemorySegment.ofAddress(name), arena));
    }

    /** A buffer for at least {@code size} handles. */
    private MemorySegment lemmaBuffer(int size)
    {
      if (lemmas.byteSize() < size * ADDRESS.byteSize())
      {
        lemmas = arena.allocate(ADDRESS, Math.max(size, 16));
      }
      return lemmas;
    }
  }

  /** {@code const Cvc5Term* (*check)(size_t* size, void* state)} */
  private static MemorySegment check(WeakReference<Plugin> ref, MemorySegment sizeOut)
  {
    MemorySegment size = sizeOut.reinterpret(JAVA_LONG.byteSize());
    size.set(JAVA_LONG, 0, 0L);
    try
    {
      Plugin plugin = ref.get();
      if (plugin == null)
      {
        return MemorySegment.NULL;
      }
      // The lemmas are copied by native code before any further Java code runs
      // on this thread, so their wrappers cannot be reclaimed first.
      MemorySegment[] lemmas = plugin.plugin.checkNative();
      if (lemmas.length == 0)
      {
        return MemorySegment.NULL;
      }
      MemorySegment buffer = plugin.lemmaBuffer(lemmas.length);
      for (int i = 0; i < lemmas.length; i++)
      {
        buffer.setAtIndex(ADDRESS, i, lemmas[i]);
      }
      size.set(JAVA_LONG, 0, (long) lemmas.length);
      return buffer;
    }
    catch (Throwable e)
    {
      size.set(JAVA_LONG, 0, 0L);
      fail("The plugin threw an exception in check()", e);
      return MemorySegment.NULL;
    }
  }

  /** {@code void (*notify_sat_clause)(const Cvc5Term clause, void* state)} */
  private static void notifySatClause(WeakReference<Plugin> ref, MemorySegment clause)
  {
    try
    {
      Plugin plugin = ref.get();
      if (plugin == null)
      {
        CApi.cvc5_term_release(clause);
        return;
      }
      // The C API transfers a reference to the clause to the callee.
      plugin.plugin.notifySatClauseNative(clause);
    }
    catch (Throwable e)
    {
      fail("The plugin threw an exception in notifySatClause()", e);
    }
  }

  /** {@code void (*notify_theory_lemma)(const Cvc5Term lemma, void* state)} */
  private static void notifyTheoryLemma(WeakReference<Plugin> ref, MemorySegment lemma)
  {
    try
    {
      Plugin plugin = ref.get();
      if (plugin == null)
      {
        CApi.cvc5_term_release(lemma);
        return;
      }
      // The C API transfers a reference to the lemma to the callee.
      plugin.plugin.notifyTheoryLemmaNative(lemma);
    }
    catch (Throwable e)
    {
      fail("The plugin threw an exception in notifyTheoryLemma()", e);
    }
  }
}
