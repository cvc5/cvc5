package cvc;

import java.io.IOException;

class Utils
{
  static
  {
    loadLibraries();
  }

  /**
   * load cvc jni library
   */
  public static void loadLibraries()
  {
    System.loadLibrary("cvcjni");
  }
}
