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

import static java.lang.foreign.ValueLayout.JAVA_LONG;

import java.lang.foreign.Arena;
import java.lang.foreign.FunctionDescriptor;
import java.lang.foreign.MemorySegment;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.ref.WeakReference;

/**
 * Upcalls from the cvc5 C API into Java: oracles and plugins.
 *
 * <p>The C API calls a callback through a function pointer, an upcall stub.
 * A stub keeps its target alive like a global reference, so a stub that
 * referenced a plugin would keep the plugin, its term manager, and thus every
 * object of that term manager reachable forever. The stubs therefore only
 * reference their callback object weakly, and the {@link Solver} keeps the
 * callback objects (and with them, the stubs) alive for as long as it exists.
 * Callbacks only happen while the solver is in use.</p>
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

  private static final MethodHandle APPLY_ORACLE;
  private static final MethodHandle CHECK;
  private static final MethodHandle NOTIFY_SAT_CLAUSE;
  private static final MethodHandle NOTIFY_THEORY_LEMMA;
  private static final MethodHandle GET_NAME;

  static
  {
    try
    {
      MethodHandles.Lookup lookup = MethodHandles.lookup();
      APPLY_ORACLE = lookup.findStatic(Callbacks.class,
          "applyOracle",
          MethodType.methodType(
              long.class, WeakReference.class, long.class, long.class, long.class));
      CHECK = lookup.findStatic(Callbacks.class,
          "check",
          MethodType.methodType(long.class, WeakReference.class, long.class, long.class));
      NOTIFY_SAT_CLAUSE = lookup.findStatic(Callbacks.class,
          "notifySatClause",
          MethodType.methodType(void.class, WeakReference.class, long.class, long.class));
      NOTIFY_THEORY_LEMMA = lookup.findStatic(Callbacks.class,
          "notifyTheoryLemma",
          MethodType.methodType(void.class, WeakReference.class, long.class, long.class));
      GET_NAME = lookup.findStatic(
          Callbacks.class, "getName", MethodType.methodType(long.class, long.class));
    }
    catch (ReflectiveOperationException e)
    {
      throw new ExceptionInInitializerError(e);
    }
  }

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
      CApi.cvc5_set_callback_error(Native.cstring(arena, message));
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
    /** The address of the upcall stub. */
    final long function;

    Oracle(NativeContext ctx, IOracle oracle)
    {
      this.ctx = ctx;
      this.oracle = oracle;
      MethodHandle target =
          MethodHandles.insertArguments(APPLY_ORACLE, 0, new WeakReference<>(this));
      function =
          Native.LINKER
              .upcallStub(
                  target, FunctionDescriptor.of(JAVA_LONG, JAVA_LONG, JAVA_LONG, JAVA_LONG), arena)
              .address();
    }
  }

  /**
   * {@code Cvc5Term (*fun)(size_t size, const Cvc5Term* args, void* state)}
   */
  private static long applyOracle(WeakReference<Oracle> ref, long size, long args, long state)
  {
    try
    {
      Oracle oracle = ref.get();
      if (oracle == null)
      {
        throw new IllegalStateException("The oracle has been reclaimed");
      }
      // The C API transfers a reference to each argument to the callee.
      Term[] terms = Utils.getTerms(oracle.ctx, Native.longs(args, size));
      Term result = oracle.oracle.apply(terms);
      if (result == null)
      {
        throw new NullPointerException("The oracle returned null");
      }
      // The result is copied by native code before any further Java code
      // runs on this thread, so its wrapper cannot be reclaimed first.
      return result.getPointer();
    }
    catch (Throwable e)
    {
      fail("The oracle threw an exception", e);
      return 0;
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
    /** The address of the {@code Cvc5Plugin} struct. */
    final long struct;

    Plugin(AbstractPlugin plugin)
    {
      this.plugin = plugin;
      WeakReference<Plugin> self = new WeakReference<>(this);
      long name = Native.cstring(arena, plugin.getName());
      // struct Cvc5Plugin: four function pointers, followed by the states of
      // the first three.
      MemorySegment s = arena.allocate(JAVA_LONG, 7);
      s.setAtIndex(JAVA_LONG,
          0,
          stub(MethodHandles.insertArguments(CHECK, 0, self),
              FunctionDescriptor.of(JAVA_LONG, JAVA_LONG, JAVA_LONG)));
      s.setAtIndex(JAVA_LONG,
          1,
          stub(MethodHandles.insertArguments(NOTIFY_SAT_CLAUSE, 0, self),
              FunctionDescriptor.ofVoid(JAVA_LONG, JAVA_LONG)));
      s.setAtIndex(JAVA_LONG,
          2,
          stub(MethodHandles.insertArguments(NOTIFY_THEORY_LEMMA, 0, self),
              FunctionDescriptor.ofVoid(JAVA_LONG, JAVA_LONG)));
      s.setAtIndex(JAVA_LONG,
          3,
          stub(MethodHandles.insertArguments(GET_NAME, 0, name), FunctionDescriptor.of(JAVA_LONG)));
      struct = s.address();
    }

    private long stub(MethodHandle target, FunctionDescriptor descriptor)
    {
      return Native.LINKER.upcallStub(target, descriptor, arena).address();
    }

    /** A buffer for at least {@code size} handles. */
    private MemorySegment lemmaBuffer(int size)
    {
      if (lemmas.byteSize() < (long) size * Long.BYTES)
      {
        lemmas = arena.allocate(JAVA_LONG, Math.max(size, 16));
      }
      return lemmas;
    }
  }

  /** {@code const Cvc5Term* (*check)(size_t* size, void* state)} */
  private static long check(WeakReference<Plugin> ref, long sizeOut, long state)
  {
    MemorySegment size = MemorySegment.ofAddress(sizeOut).reinterpret(Long.BYTES);
    size.set(JAVA_LONG, 0, 0L);
    try
    {
      Plugin plugin = ref.get();
      if (plugin == null)
      {
        return 0;
      }
      // The lemmas are copied by native code before any further Java code runs
      // on this thread, so their wrappers cannot be reclaimed first.
      long[] lemmas = plugin.plugin.checkNative();
      if (lemmas.length == 0)
      {
        return 0;
      }
      MemorySegment buffer = plugin.lemmaBuffer(lemmas.length);
      MemorySegment.copy(lemmas, 0, buffer, JAVA_LONG, 0, lemmas.length);
      size.set(JAVA_LONG, 0, (long) lemmas.length);
      return buffer.address();
    }
    catch (Throwable e)
    {
      size.set(JAVA_LONG, 0, 0L);
      fail("The plugin threw an exception in check()", e);
      return 0;
    }
  }

  /** {@code void (*notify_sat_clause)(const Cvc5Term clause, void* state)} */
  private static void notifySatClause(WeakReference<Plugin> ref, long clause, long state)
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
  private static void notifyTheoryLemma(WeakReference<Plugin> ref, long lemma, long state)
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

  /** {@code const char* (*get_name)()}, bound to the name of the plugin. */
  private static long getName(long name)
  {
    return name;
  }
}
