/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Daniel Larraz, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

/**
 * A utility class containing static helper methods commonly used across the application.
 * <p>
 * This class is not meant to be instantiated. All methods are static and stateless.
 */
public final class Utils
{
  /**
   * Represent the operating system types supported by cvc5.
   *
   * It includes logic to detect the current operating system at runtime.
   */
  public enum OS {
    /**
     * Microsoft Windows operating system.
     */
    WINDOWS,
    /**
     * Apple macOS operating system.
     */
    OSX,
    /**
     * Linux-based operating system.
     */
    LINUX,
    /**
     * Unknown or unsupported operating system.
     */
    UNKNOWN;

    /**
     * The detected operating system on which the application is currently running.
     */
    public static final OS CURRENT = detectOS();

    /**
     * Detect the current operating system by examining the {@code os.name} system property.
     *
     * @return the {@link OS} enum constant that matches the current operating system,
     *         or {@link #UNKNOWN} if it cannot be determined.
     */
    private static OS detectOS()
    {
      String osName = System.getProperty("os.name").toLowerCase(Locale.ROOT);
      if (osName.startsWith("windows"))
        return WINDOWS;
      if (osName.startsWith("mac"))
        return OSX;
      if (osName.startsWith("linux"))
        return LINUX;
      return UNKNOWN;
    }
  }

  /**
   * Represent the CPU architecture supported by cvc5.
   *
   * It includes logic to detect the current CPU architecture at runtime.
   */
  public enum CPUArchitecture {
    /**
     * ARMv8 64 bit.
     */
    AARCH_64,
    /**
     * Intel x86_64/AMD 64 bit.
     */
    X86_64,
    /**
     * Unknown or unsupported CPU architecture.
     */
    UNKNOWN;

     /**
     * The detected CPU architecture on which the application is currently running.
     */
    public static final CPUArchitecture CURRENT = detectCPUArchitecture();

    /**
     * Detect the current CPU architecture by examining the {@code os.arch} system property.
     *
     * @return the {@link CPUArchitecture} enum constant that matches the current CPU architecture,
     *         or {@link #UNKNOWN} if it cannot be determined.
     */
    private static CPUArchitecture detectCPUArchitecture()
    {
      String osArch = System.getProperty("os.arch").toLowerCase(Locale.ROOT);
      switch (osArch) {
        case "aarch64":
          return AARCH_64;
        case "amd64":
        case "x86_64":
          return X86_64;
        default:
          return UNKNOWN;
      }
    }
  }

  /**
   * The base path inside the JAR where native libraries are stored.
   */
  public static final String LIBPATH_IN_JAR = "/cvc5-libs";

  /**
   * Flag indicating whether the native cvc5 libraries have already been loaded.
   */
  private static boolean areLibrariesLoaded = false;

  static
  {
    loadLibraries();
  }

  /**
   * Private constructor to prevent instantiation of this utility class.
   */
  private Utils() {}

  /**
   * Transfer all bytes from the provided {@link InputStream} to the specified
   * {@link FileOutputStream}.
   *
   * <p>Note: This method replicates the functionality of InputStream#transferTo(OutputStream),
   * which was introduced in Java 9 (currently, the minimum required Java version is 1.8)</p>
   *
   * @param inputStream The input stream from which data is read
   * @param outputStream The output stream to which data is written
   * @throws IOException If an I/O error occurs during reading or writing
   */
  public static void transferTo(InputStream inputStream, FileOutputStream outputStream)
      throws IOException
  {
    byte[] buffer = new byte[4096];
    int bytesRead;
    while ((bytesRead = inputStream.read(buffer)) != -1)
    {
      outputStream.write(buffer, 0, bytesRead);
    }
  }

  /**
   * Load a native library from a specified path within a JAR file and loads it into the JVM.
   *
   * @param tempDir The temporary directory where the extracted native library will be written.
   * @param path The path inside the JAR where the library is located (e.g., "/cvc5-libs").
   * @param filename The name of the library file (e.g., "libcvc5.so").
   * @throws FileNotFoundException If the library cannot be found
   * @throws Exception If an I/O error occurs or the library cannot be loaded
   */
  public static void loadLibraryFromJar(Path tempDir, String path, String filename)
    throws FileNotFoundException, Exception
  {
    String pathInJar = path + "/" + filename;
    // Extract the library from the JAR
    InputStream inputStream = Utils.class.getResourceAsStream(pathInJar);
    if (inputStream == null)
    {
      throw new FileNotFoundException("Library not found: " + pathInJar);
    }

    // Create a temporary file for the native library
    File tempLibrary = tempDir.resolve(filename).toFile();
    tempLibrary.deleteOnExit(); // Mark the file for deletion on exit

    // Write the extracted library to the temp file
    try (FileOutputStream outputStream = new FileOutputStream(tempLibrary))
    {
      transferTo(inputStream, outputStream);
    }

    // Load the library
    try
    {
      System.load(tempLibrary.getAbsolutePath());
    }
    catch (UnsatisfiedLinkError e)
    {
      throw new Exception("Couldn't load cvc5 native libraries from JAR");
    }
  }

  /**
   * Load cvc5 native libraries.
   */
  public static void loadLibraries()
  {
    if (!areLibrariesLoaded && !Boolean.parseBoolean(System.getProperty("cvc5.skipLibraryLoad")))
    {
      try
      {
        String filename;
        switch (OS.CURRENT)
        {
          case WINDOWS: filename = "cvc5jni.dll"; break;
          case OSX: filename = "libcvc5jni.dylib"; break;
          default:
            // We assume it is Linux or a Unix-based system.
            // If not, there's nothing more we can do anyway.
            filename = "libcvc5jni.so";
        }

        String subdir = "/" + OS.CURRENT.name() + "/" + CPUArchitecture.CURRENT.name();
        subdir = subdir.toLowerCase(Locale.ROOT);
        // Create a temporary directory to store the libraries
        Path tempDir = Files.createTempDirectory("cvc5-libs");
        tempDir.toFile().deleteOnExit(); // Mark the directory for deletion on exit

        loadLibraryFromJar(tempDir, LIBPATH_IN_JAR + subdir, filename);
      }
      catch (Exception ex)
      {
        try
        {
          System.loadLibrary("cvc5jni");
        }
        catch (UnsatisfiedLinkError jni_ex)
        {
          throw new UnsatisfiedLinkError("Couldn't load cvc5 native libraries");
        }
      }
      areLibrariesLoaded = true;
    }
  }

  /**
   * Construct an array of {@link Sort} objects from an array of native pointers.
   *
   * @return Sorts array from array of Sort pointers.
   * @param pointers The array of pointers.
   */
  public static Sort[] getSorts(long[] pointers)
  {
    Sort[] sorts = new Sort[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      sorts[i] = new Sort(pointers[i]);
    }
    return sorts;
  }

  /**
   * Construct an array of {@link Term} objects from an array of native pointers.
   *
   * @return Terms array from array of Term pointers.
   * @param pointers The array of pointers.
   */
  public static Term[] getTerms(long[] pointers)
  {
    Term[] terms = new Term[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      terms[i] = new Term(pointers[i]);
    }
    return terms;
  }

  /**
   * Construct an array of {@link Proof} objects from an array of native pointers.
   *
   * @return proofs array from array of Proof pointers
   * @param pointers The array of pointers.
   */
  public static Proof[] getProofs(long[] pointers)
  {
    Proof[] proofs = new Proof[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      proofs[i] = new Proof(pointers[i]);
    }
    return proofs;
  }

  /**
   * Extract native pointer values from a one-dimensional array of {@link IPointer} objects.
   *
   * @return Pointers from one dimensional array.
   * @param objects The one dimensional array of pointers.
   */
  public static long[] getPointers(IPointer[] objects)
  {
    long[] pointers = new long[objects.length];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = objects[i].getPointer();
    }
    return pointers;
  }

  /**
   * Extract native pointer values from a two-dimensional matrix of {@link IPointer} objects.
   *
   * @return Pointers from two dimensional matrix.
   * @param objects The two dimensional array of pointers.
   */
  public static long[][] getPointers(IPointer[][] objects)
  {
    long[][] pointers = new long[objects.length][];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = new long[objects[i].length];
      for (int j = 0; j < objects[i].length; j++)
      {
        pointers[i][j] = objects[i][j].getPointer();
      }
    }
    return pointers;
  }

  /**
   * Validate that the specified integer is non-negative (unsigned).
   *
   * @param integer The integer value to validate
   * @param name A name to use in the exception message for identification
   * @throws CVC5ApiException if the value is negative
   */
  public static void validateUnsigned(int integer, String name) throws CVC5ApiException
  {
    if (integer < 0)
    {
      throw new CVC5ApiException("Expected " + name + " '" + integer + "' to be non negative.");
    }
  }

  /**
   * Validate that the specified long integer is non-negative (unsigned).
   *
   * @param integer The long value to validate
   * @param name A name to use in the exception message for identification
   * @throws CVC5ApiException if the value is negative
   */
  public static void validateUnsigned(long integer, String name) throws CVC5ApiException
  {
    if (integer < 0)
    {
      throw new CVC5ApiException("Expected " + name + " '" + integer + "' to be non negative.");
    }
  }

  /**
   * Validate that all elements in the given array are non-negative (unsigned).
   *
   * @param integers The array of integers to validate
   * @param name A name to use in the exception message for identification
   * @throws CVC5ApiException if any element in the array is negative
   */
  public static void validateUnsigned(int[] integers, String name) throws CVC5ApiException
  {
    for (int i = 0; i < integers.length; i++)
    {
      if (integers[i] < 0)
      {
        throw new CVC5ApiException(
            "Expected " + name + "[" + i + "] '" + integers[i] + "' to be non negative.");
      }
    }
  }

  /**
   * Validate that all elements in the given array are non-negative (unsigned).
   *
   * @param integers The array of long integers to validate
   * @param name A name to use in the exception message for identification
   * @throws CVC5ApiException if any element in the array is negative
   */
  public static void validateUnsigned(long[] integers, String name) throws CVC5ApiException
  {
    for (int i = 0; i < integers.length; i++)
    {
      if (integers[i] < 0)
      {
        throw new CVC5ApiException(
            "Expected " + name + "[" + i + "] '" + integers[i] + "' to be non negative.");
      }
    }
  }

  /**
   * Convert an array of {@code Pair} objects, where the second element extends {@link
   * AbstractPointer}, into an array of {@code Pair} objects with the second element as a {@code
   * Long} representing the native pointer.
   *
   * @param <K> The type of the first element in the pairs.
   * @param abstractPointers The input array of pairs with {@code AbstractPointer} as the second
   *     element.
   * @return An array of pairs where the second element is the native pointer value as a {@code
   *     Long}.
   */
  @SuppressWarnings("unchecked")
  public static <K> Pair<K, Long>[] getPairs(Pair<K, ? extends AbstractPointer>[] abstractPointers)
  {
    Pair<K, Long>[] pointers = new Pair[abstractPointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = new Pair<>(abstractPointers[i].first, abstractPointers[i].second.getPointer());
    }
    return pointers;
  }

  /**
   * Convert a rational string a/b to a pair of BigIntegers
   * @param rational The rational string.
   * @return The pair of big integers.
   */
  public static Pair<BigInteger, BigInteger> getRational(String rational)
  {
    if (rational.contains("/"))
    {
      String[] pair = rational.split("/");
      return new Pair<>(new BigInteger(pair[0]), new BigInteger(pair[1]));
    }
    return new Pair<>(new BigInteger(rational), new BigInteger("1"));
  }

  /**
   * Convert a pair of BigIntegers to a rational string a/b
   * @param pair The pair of big integers.
   * @return The rational string.
   */
  public static String getRational(Pair<BigInteger, BigInteger> pair)
  {
    return pair.first.toString() + "/" + pair.second.toString();
  }
}
