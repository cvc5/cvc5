package cvc;

public class Configuration
{
  public native static String getName();

  public native static boolean isDebugBuild();

  public native static boolean isStatisticsBuild();

  public native static boolean isTracingBuild();

  public native static boolean isDumpingBuild();

  public native static boolean isMuzzledBuild();

  public native static boolean isAssertionBuild();

  public native static boolean isProofBuild();

  public native static boolean isCoverageBuild();

  public native static boolean isProfilingBuild();

  public native static boolean isAsanBuild();

  public native static boolean isUbsanBuild();

  public native static boolean isTsanBuild();

  public native static boolean isCompetitionBuild();

  public native static boolean isStaticBuild();

  public native static String getPackageName();

  public native static String getVersionString();

  public native static int getVersionMajor();

  public native static int getVersionMinor();

  public native static int getVersionRelease();

  public native static String getVersionExtra();

  public native static String copyright();

  public native static String about();

  public native static boolean licenseIsGpl();

  public native static boolean isBuiltWithGmp();

  public native static boolean isBuiltWithCln();

  public native static boolean isBuiltWithGlpk();

  public native static boolean isBuiltWithAbc();

  public native static boolean isBuiltWithCadical();

  public native static boolean isBuiltWithCryptominisat();

  public native static boolean isBuiltWithKissat();

  public native static boolean isBuiltWithDrat2Er();

  public native static boolean isBuiltWithEditline();

  public native static boolean isBuiltWithLfsc();

  public native static boolean isBuiltWithPoly();

  public native static boolean isBuiltWithSymFPU();

  /* Return the number of debug tags */
  public native static int getNumDebugTags();

  /* Return a sorted array of the debug tags name */
  public native static String[] getDebugTags();

  /* Test if the given argument is a known debug tag name */
  public native static boolean isDebugTag(String tag);

  /* Return the number of trace tags */
  public native static int getNumTraceTags();

  /* Return a sorted array of the trace tags name */
  public native static String[] getTraceTags();

  /* Test if the given argument is a known trace tag name */
  public native static boolean isTraceTag(String tag);

  public native static boolean isGitBuild();

  public native static String getGitBranchName();

  public native static String getGitCommit();

  public native static boolean hasGitModifications();

  public native static String getGitId();

  public native static String getCompiler();

  public native static String getCompiledDateTime();
}
