package cvc;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.lang.ref.Cleaner;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;

class Utils
{
  static final Cleaner cleaner = Cleaner.create();

  static final String osName = System.getProperty("os.name");

  static
  {
    loadLibraries();
  }

  /**
   * @return the absolute path of cvcJavaApi dynamic library
   */
  private static String getCvcApiLibFile() throws IOException
  {
    String cvcApiLibName;
    if (osName.startsWith("Linux"))
    {
      cvcApiLibName = "libcvcJavaApi.so";
    }
    else if (osName.startsWith("Mac"))
    {
      cvcApiLibName = "libcvcJavaApi.dylib";
    }
    else if (osName.startsWith("Windows"))
    {
      cvcApiLibName = "cvcJavaApi.dll";
    }
    else
    {
      throw new RuntimeException("The operating system '" + osName + "' is not supported");
    }
    String cvcApiLibFile =
        System.getProperty("java.io.tmpdir") + File.separatorChar + cvcApiLibName;
    if (Files.exists(Path.of(cvcApiLibFile)))
    {
      // return if the library exists in the temp directory
      // return cvcApiLibFile; // TODO: this is disabled for development. Enable this before release
    }
    // copy the library from resources to the temp directory
    InputStream input = Solver.class.getResourceAsStream("/" + cvcApiLibName);
    Files.copy(input, Paths.get(cvcApiLibFile), StandardCopyOption.REPLACE_EXISTING);
    return cvcApiLibFile;
  }

  public static void loadLibraries()
  {
    try
    {
      String cvcApiLibFile = getCvcApiLibFile();
      System.load(cvcApiLibFile);
    }
    catch (IOException e)
    {
      e.printStackTrace();
    }
  }

  public static long[] getPointers(IPointer[] objects)
  {
    long[] pointers = new long[objects.length];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = objects[i].getPointer();
    }
    return pointers;
  }

  public static Sort[] getSorts(Solver solver, long[] pointers)
  {
    Sort[] sorts = new Sort[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      sorts[i] = new Sort(solver, pointers[i]);
    }
    return sorts;
  }

  public static <K> Pair<K, Long>[] getPairs(Pair<K, ? extends AbstractPointer>[] abstractPointers)
  {
    Pair<K, Long>[] pointers = new Pair[abstractPointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = new Pair<>(abstractPointers[i].first, abstractPointers[i].second.getPointer());
    }
    return pointers;
  }
}
