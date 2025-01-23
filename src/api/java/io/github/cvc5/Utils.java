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
import java.util.List;

public class Utils
{
  public static final String LIBPATH_IN_JAR = "/cvc5-libs";

  private static boolean areLibrariesLoaded = false;

  static
  {
    loadLibraries();
  }

  /**
   * Reads a text file from the specified path within the JAR file and returns a list of library
   * filenames.
   * @param pathInJar The path to the text file inside the JAR
   * @return a list of filenames read from the file
   * @throws FileNotFoundException If the text file does not exist
   * @throws IOException If an I/O error occurs
   */
  public static List<String> readLibraryFilenames(String pathInJar)
      throws FileNotFoundException, IOException
  {
    List<String> filenames = new ArrayList<>();

    // Load the input stream from the resource path within the JAR
    try (InputStream inputStream = Utils.class.getResourceAsStream(pathInJar))
    {
      // Check if the input stream is null (resource not found)
      if (inputStream == null)
      {
        throw new FileNotFoundException("Resource not found: " + pathInJar);
      }

      try (BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream)))
      {
        String line;
        // Read each line from the file and add it to the list
        while ((line = reader.readLine()) != null)
        {
          filenames.add(line);
        }
      }
    }

    return filenames;
  }

  /**
   * Transfers all bytes from the provided {@link InputStream} to the specified {@link
   * FileOutputStream}.
   *
   * <p>Note: This method replicates the functionality of {@link
   * InputStream#transferTo(OutputStream)}, which was introduced in Java 9 (currently, the minimum
   * required Java version is 1.8)</p>
   *
   * @param inputStream The input stream from which data is read
   * @param outputStream The output stream to which data is written
   * @throws IOException If an I/O error occurs during reading or writing
   * @see InputStream#transferTo(OutputStream)
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
   * Loads a native library from a specified path within a JAR file and loads it into the JVM.
   *
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
        // Try to extract the libraries from a JAR in the classpath
        List<String> filenames = readLibraryFilenames(LIBPATH_IN_JAR + "/filenames.txt");

        // Create a temporary directory to store the libraries
        Path tempDir = Files.createTempDirectory("cvc5-libs");
        tempDir.toFile().deleteOnExit(); // Mark the directory for deletion on exit

        for (String filename : filenames)
        {
          loadLibraryFromJar(tempDir, LIBPATH_IN_JAR, filename);
        }
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
   * @return proofs array from array of pointers
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

  public static void validateUnsigned(int integer, String name) throws CVC5ApiException
  {
    if (integer < 0)
    {
      throw new CVC5ApiException("Expected " + name + " '" + integer + "' to be non negative.");
    }
  }

  public static void validateUnsigned(long integer, String name) throws CVC5ApiException
  {
    if (integer < 0)
    {
      throw new CVC5ApiException("Expected " + name + " '" + integer + "' to be non negative.");
    }
  }

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
