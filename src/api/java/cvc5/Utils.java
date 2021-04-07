package cvc5;

import java.io.IOException;

class Utils
{
  static
  {
    loadLibraries();
  }

  /**
   * load cvc5 jni library
   */
  public static void loadLibraries()
  {
    System.loadLibrary("cvc5jni");
  }
}
