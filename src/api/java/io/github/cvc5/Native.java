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

import static java.lang.foreign.ValueLayout.JAVA_INT;
import static java.lang.foreign.ValueLayout.JAVA_LONG;

import java.lang.foreign.Arena;
import java.lang.foreign.FunctionDescriptor;
import java.lang.foreign.Linker;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.SymbolLookup;
import java.lang.invoke.MethodHandle;
import java.nio.charset.StandardCharsets;

/**
 * Access to the cvc5 C API through the Foreign Function &amp; Memory API.
 *
 * <p>The raw bindings of the C API are generated into {@link CApi}. This
 * class loads the native library, creates the downcall handles for
 * {@link CApi}, raises C API errors as Java exceptions, and converts strings
 * and arrays between Java and native memory.</p>
 *
 * <p>The C API reports errors through thread-local state that is reset at the
 * beginning of each call. {@link CApi} therefore checks it right after each
 * call, on the same thread. Strings and arrays returned by the C API live in
 * thread-local buffers that are only valid until the next call of the same
 * function, so they are copied immediately.</p>
 */
final class Native
{
  private Native() {}

  /** Error kinds, see {@code Cvc5ErrorKind} in the C API. */
  private static final int ERROR_KIND_RECOVERABLE = 2;
  private static final int ERROR_KIND_OPTION = 3;
  private static final int ERROR_KIND_PARSER = 4;
  private static final int ERROR_KIND_OUT_OF_MEMORY = 5;

  /** A symbol that every native library providing the C API defines. */
  private static final String PROBE_SYMBOL = "cvc5_term_manager_new";

  static final Linker LINKER = Linker.nativeLinker();

  /** Looks up the functions of the C API. */
  static final SymbolLookup LOOKUP = loadLookup();

  private static SymbolLookup loadLookup()
  {
    Utils.loadLibraries();
    SymbolLookup lookup = SymbolLookup.loaderLookup();
    if (lookup.find(PROBE_SYMBOL).isEmpty())
    {
      // With dynamic linking, the C API is defined by the cvc5 libraries that
      // the cvc5jni library depends on. Depending on the platform, symbols of
      // dependencies cannot be looked up through the dependent library, so
      // load them explicitly.
      for (String name : new String[] {"cvc5", "libcvc5", "cvc5parser", "libcvc5parser"})
      {
        try
        {
          System.loadLibrary(name);
        }
        catch (UnsatisfiedLinkError e)
        {
          // try the next name
        }
      }
      lookup = SymbolLookup.loaderLookup();
      if (lookup.find(PROBE_SYMBOL).isEmpty())
      {
        throw new UnsatisfiedLinkError("Couldn't find the cvc5 C API in the cvc5 native libraries");
      }
    }
    return lookup;
  }

  /**
   * Create a downcall handle for a function of the C API.
   *
   * @param name The name of the C function.
   * @param descriptor The function descriptor.
   * @param options The linker options.
   * @return The downcall handle.
   */
  static MethodHandle downcall(String name, FunctionDescriptor descriptor, Linker.Option... options)
  {
    MemorySegment symbol = LOOKUP.find(name).orElseThrow(
        () -> new UnsatisfiedLinkError("Undefined C API function " + name));
    return LINKER.downcallHandle(symbol, descriptor, options);
  }

  /**
   * Wrap an exception thrown by a downcall handle itself (not by cvc5).
   *
   * @param t The exception.
   * @return An unchecked exception to throw.
   */
  static RuntimeException unexpected(Throwable t)
  {
    if (t instanceof RuntimeException)
    {
      return (RuntimeException) t;
    }
    if (t instanceof Error)
    {
      throw (Error) t;
    }
    return new IllegalStateException(t);
  }

  /**
   * Raise the error of the most recent C API call on this thread, if any.
   *
   * <p>Errors are mapped to the exception types of the Java API according to
   * their kind. A parser error raises a {@link CVC5ParserException}, which is
   * a checked exception, regardless of whether the calling method declares
   * it, as native methods did when the Java API was based on JNI.</p>
   */
  static void checkError()
  {
    if (CApi.cvc5_has_error())
    {
      int kind = CApi.cvc5_get_error_kind();
      String message = string(CApi.cvc5_get_error_message());
      switch (kind)
      {
        case ERROR_KIND_OPTION: throw new CVC5ApiOptionException(message);
        case ERROR_KIND_RECOVERABLE: throw new CVC5ApiRecoverableException(message);
        case ERROR_KIND_PARSER:
          throw Native.<RuntimeException>sneaky(new CVC5ParserException(message));
        case ERROR_KIND_OUT_OF_MEMORY: throw new OutOfMemoryError(message);
        default: throw Callbacks.withCause(new CVC5ApiException(message), message);
      }
    }
  }

  @SuppressWarnings("unchecked")
  private static <T extends Throwable> T sneaky(Throwable t) throws T
  {
    throw (T) t;
  }

  /* .................................................................... */
  /* Strings                                                              */
  /* .................................................................... */

  /**
   * Copy a NUL-terminated UTF-8 string from native memory.
   *
   * @param pointer The address of the string, or 0.
   * @return The string, or {@code null} if {@code pointer} is 0.
   */
  static String string(long pointer)
  {
    if (pointer == 0)
    {
      return null;
    }
    return MemorySegment.ofAddress(pointer).reinterpret(Long.MAX_VALUE).getString(0);
  }

  /**
   * Copy a NUL-terminated UTF-32 string from native memory.
   *
   * @param pointer The address of the string.
   * @return The string.
   */
  static String u32string(long pointer)
  {
    MemorySegment s = MemorySegment.ofAddress(pointer).reinterpret(Long.MAX_VALUE);
    StringBuilder b = new StringBuilder();
    for (long i = 0;; i += 4)
    {
      int c = s.get(JAVA_INT, i);
      if (c == 0)
      {
        return b.toString();
      }
      b.appendCodePoint(c);
    }
  }

  /**
   * Copy an array of {@code size} NUL-terminated UTF-8 strings from native
   * memory.
   *
   * @param pointer The address of the array of string pointers.
   * @param size The number of strings.
   * @return The strings.
   */
  static String[] strings(long pointer, long size)
  {
    long[] pointers = longs(pointer, size);
    String[] res = new String[pointers.length];
    for (int i = 0; i < res.length; i++)
    {
      res[i] = string(pointers[i]);
    }
    return res;
  }

  /**
   * Allocate a NUL-terminated UTF-8 string in native memory.
   *
   * @param arena The arena to allocate in.
   * @param s The string.
   * @return The address of the native string.
   */
  static long cstring(Arena arena, String s)
  {
    return arena.allocateFrom(s, StandardCharsets.UTF_8).address();
  }

  /**
   * Allocate a NUL-terminated UTF-32 string in native memory.
   *
   * @param arena The arena to allocate in.
   * @param s The string.
   * @return The address of the native string.
   */
  static long u32string(Arena arena, String s)
  {
    int[] codePoints = s.codePoints().toArray();
    MemorySegment seg = arena.allocate(JAVA_INT, codePoints.length + 1);
    MemorySegment.copy(codePoints, 0, seg, JAVA_INT, 0, codePoints.length);
    return seg.address();
  }

  /**
   * Allocate an array of NUL-terminated UTF-8 strings in native memory.
   *
   * @param arena The arena to allocate in.
   * @param strings The strings.
   * @return The address of the native array of string pointers.
   */
  static long cstrings(Arena arena, String[] strings)
  {
    long[] pointers = new long[strings.length];
    for (int i = 0; i < strings.length; i++)
    {
      pointers[i] = cstring(arena, strings[i]);
    }
    return longs(arena, pointers);
  }

  /* .................................................................... */
  /* Arrays                                                               */
  /* .................................................................... */

  /**
   * Allocate an array of {@code long}s (e.g., handles) in native memory.
   *
   * @param arena The arena to allocate in.
   * @param values The values.
   * @return The address of the native array.
   */
  static long longs(Arena arena, long[] values)
  {
    MemorySegment seg = arena.allocate(JAVA_LONG, Math.max(1, values.length));
    MemorySegment.copy(values, 0, seg, JAVA_LONG, 0, values.length);
    return seg.address();
  }

  /**
   * Allocate an array of {@code int}s (e.g., enum values or {@code uint32_t}s)
   * in native memory.
   *
   * @param arena The arena to allocate in.
   * @param values The values.
   * @return The address of the native array.
   */
  static long ints(Arena arena, int[] values)
  {
    MemorySegment seg = arena.allocate(JAVA_INT, Math.max(1, values.length));
    MemorySegment.copy(values, 0, seg, JAVA_INT, 0, values.length);
    return seg.address();
  }

  /**
   * Copy an array of {@code size} {@code long}s (e.g., handles) from native
   * memory.
   *
   * @param pointer The address of the array (may be 0 if {@code size} is 0).
   * @param size The number of elements.
   * @return The values.
   */
  static long[] longs(long pointer, long size)
  {
    if (size == 0)
    {
      return new long[0];
    }
    return MemorySegment.ofAddress(pointer).reinterpret(size * Long.BYTES).toArray(JAVA_LONG);
  }

  /**
   * Copy an array of {@code size} {@code int}s from native memory.
   *
   * @param pointer The address of the array (may be 0 if {@code size} is 0).
   * @param size The number of elements.
   * @return The values.
   */
  static int[] ints(long pointer, long size)
  {
    if (size == 0)
    {
      return new int[0];
    }
    return MemorySegment.ofAddress(pointer).reinterpret(size * Integer.BYTES).toArray(JAVA_INT);
  }

  /**
   * Allocate an output parameter of type {@code size_t}, {@code int64_t} or
   * a pointer.
   *
   * @param arena The arena to allocate in.
   * @return The output parameter.
   */
  static MemorySegment outLong(Arena arena)
  {
    return arena.allocate(JAVA_LONG);
  }

  /**
   * Allocate an output parameter of type {@code int32_t} or {@code uint32_t}.
   *
   * @param arena The arena to allocate in.
   * @return The output parameter.
   */
  static MemorySegment outInt(Arena arena)
  {
    return arena.allocate(JAVA_INT);
  }
}
