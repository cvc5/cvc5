package cvc5;

import java.io.*;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.regex.Pattern;

/**
 * class for loading native libraries
 */
public class NativeCode
{
  /** names of native libraries */
  static String[] copyLibraries = new String[] {"cvc5", "cvc5jni"};

  /** names of jni native libraries that need to be loaded*/
  static String[] jniLibraries = new String[] {"cvc5jni"};

  /** cvc5 version */
  public static final String version = "0.0.0";

  /** cvc5 name */
  public static final String cvc5HomeName = "cvc5";

  /**
   * This variable caches the result of cvc5Home() function call.
   */
  private static String cvc5Home = null;

  /**
   * The system-specific file separator (/ or \)
   */
  private static final char fs = File.separatorChar;

  /**
   * Find a temporary directory to store cvc5 files; it's guaranteed to be a
   * canonical absolute path.
   */
  private static synchronized String cvc5Home()
  {
    if (cvc5Home != null)
    {
      return cvc5Home;
    }
    else
    {
      String tmpPath = System.getProperty("java.io.tmpdir");
      if (tmpPath == null || tmpPath.length() == 0)
      {
        System.out.println(
            "Error. JVM need to specify a temporary directory using java.io.tmpdir property.");
      }
      // e.g. /tmp/cvc5/0.0.0/amd64-linux
      String tmp = tmpPath + fs + cvc5HomeName + fs + version + fs + platform.dir;
      File tmpDirectory = new File(tmp);
      tmpDirectory.mkdirs();
      cvc5Home = tmpDirectory.getAbsolutePath();
    }
    System.out.println("cvc5 home: " + cvc5Home);
    System.setProperty("java.library.path", cvc5Home());
    return cvc5Home;
  }

  /**
   * Copy the given file from JAR into the destination file; if the destination
   * file exists, we then do nothing. Returns true iff a file was created and
   * written.
   */
  private static void copy(String source, String destination)
  {
    System.out.println("source: " + source);
    System.out.println("destination: " + destination);
    File destinationFile = new File(destination);
    if (destinationFile.isFile() && destinationFile.length() > 0)
    {
      return;
    }
    try
    {
      URL resourceUrl = NativeCode.class.getClassLoader().getResource(source);
      if (resourceUrl == null)
      {
        throw new RuntimeException("Could not find resource " + resourceUrl);
      }
      Files.copy(
          resourceUrl.openStream(), destinationFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
    }
    catch (IOException e)
    {
      throw new RuntimeException(e);
    }
  }

  /**
   * Copy libraries from the jar file to cvc5 home directory
   */
  static void copyLibraries()
  {
    String prefix = platform.dir + "/";
    for (String name : copyLibraries)
    {
      String libName = System.mapLibraryName(name);
      String source = prefix + libName;
      String destination = cvc5Home() + fs + libName;
      copy(source, destination);
    }
  }

  /** load jni library with the given name */
  public static void loadLibrary(String name) throws RuntimeException
  {
    try
    {
      String libraryName = System.mapLibraryName(name);
      String libraryPath = cvc5Home() + fs + libraryName;
      System.load(libraryPath);
    }
    catch (Exception e)
    {
      throw new RuntimeException(e);
    }
  }

  /** Load jni libraries */
  public static void loadLibraries()
  {
    copyLibraries();
    for (String name : jniLibraries)
    {
      NativeCode.loadLibrary(name);
    }
  }

  static class Platform
  {
    public Platform(String osnames, String osarch, String dir)
    {
      try
      {
        this.osarch = Pattern.compile(osarch, Pattern.CASE_INSENSITIVE);
        this.osname = Pattern.compile(osnames, Pattern.CASE_INSENSITIVE);
        this.dir = dir;
      }
      catch (Exception e)
      {
        e.printStackTrace();
        throw new RuntimeException(e);
      }
    }

    final Pattern osname;
    final Pattern osarch;
    final String dir;
  }

  public static Platform AMD64_LINUX = new Platform("linux", "amd64", "amd64-linux");
  public static Platform X86_LINUX = new Platform("linux", ".*86.*", "x86-linux");
  public static Platform X86_MAC =
      new Platform("mac\\s*os.*", "ppc|power|powerpc.*|x86.*", "x86-mac");
  public static Platform X86_WINDOWS = new Platform("win.*", "x86.*", "x86-windows");
  public static Platform[] platforms = {AMD64_LINUX, X86_LINUX, X86_MAC, X86_WINDOWS};

  public static Platform platform = findPlatform();

  private static Platform findPlatform()
  {
    String os = System.getProperty("os.name");
    String arch = System.getProperty("os.arch");
    System.out.println("OS _ ARCH = '" + os + "' - '" + arch + "'");
    for (Platform p : platforms)
    {
      if (p.osarch.matcher(arch).matches() && p.osname.matcher(os).matches())
      {
        System.out.println("Found = '" + p.dir);
        return platform = p;
      }
    }
    return new Platform(".*", ".*", null);
  }
}
