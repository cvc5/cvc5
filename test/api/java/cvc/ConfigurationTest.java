package cvc;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import org.junit.jupiter.api.Test;

class ConfigurationTest
{
  static
  {
    Utils.loadLibraries();
  }

  @Test void getName()
  {
    System.out.println(Configuration.getName());
  }

  @Test void isDebugBuild() {}

  @Test void isStatisticsBuild() {}

  @Test void isTracingBuild() {}

  @Test void isDumpingBuild() {}

  @Test void isMuzzledBuild() {}

  @Test void isAssertionBuild() {}

  @Test void isProofBuild() {}

  @Test void isCoverageBuild() {}

  @Test void isProfilingBuild() {}

  @Test void isAsanBuild() {}

  @Test void isUbsanBuild() {}

  @Test void isTsanBuild() {}

  @Test void isCompetitionBuild() {}

  @Test void isStaticBuild() {}

  @Test void getPackageName()
  {
    System.out.println(Configuration.getPackageName());
  }

  @Test void getVersionString()
  {
    System.out.println(Configuration.getVersionString());
  }

  @Test void getVersionMajor()
  {
    System.out.println(Configuration.getVersionMajor());
  }

  @Test void getVersionMinor()
  {
    System.out.println(Configuration.getVersionMinor());
  }

  @Test void getVersionRelease()
  {
    System.out.println(Configuration.getVersionRelease());
  }

  @Test void getVersionExtra()
  {
    System.out.println(Configuration.getVersionExtra());
  }

  @Test void copyright()
  {
    System.out.println(Configuration.copyright());
  }

  @Test void about()
  {
    System.out.println(Configuration.about());
  }

  @Test void licenseIsGpl()
  {
    System.out.println(Configuration.licenseIsGpl());
  }

  @Test void isBuiltWithGmp()
  {
    System.out.println(Configuration.isBuiltWithGmp());
  }

  @Test void isBuiltWithCln() {}

  @Test void isBuiltWithGlpk() {}

  @Test void isBuiltWithAbc() {}

  @Test void isBuiltWithCadical() {}

  @Test void isBuiltWithCryptominisat() {}

  @Test void isBuiltWithKissat() {}

  @Test void isBuiltWithDrat2Er() {}

  @Test void isBuiltWithEditline() {}

  @Test void isBuiltWithLfsc() {}

  @Test void isBuiltWithPoly() {}

  @Test void isBuiltWithSymFPU() {}

  @Test void getNumDebugTags()
  {
    System.out.println(Configuration.getNumDebugTags());
  }

  @Test void getDebugTags()
  {
    String[] tags = Configuration.getDebugTags();
    System.out.println("Number of debug tags: " + tags.length);
    for (int i = 0; i < tags.length; i++)
    {
      System.out.println(tags[i]);
    }
  }

  @Test void isDebugTag()
  {
    if (Configuration.isDebugBuild())
    {
      assertTrue(Configuration.isDebugTag("arith::eq"));
      assertFalse(Configuration.isDebugTag("arith::::eq"));
    }
    else
    {
      assertFalse(Configuration.isDebugTag("arith::eq"));
      assertFalse(Configuration.isDebugTag("arith::::eq"));
    }
  }

  @Test void getNumTraceTags() {}

  @Test void getTraceTags()
  {
    String[] tags = Configuration.getTraceTags();
    System.out.println("Number of trace tags: " + tags.length);
    for (int i = 0; i < tags.length; i++)
    {
      System.out.println(tags[i]);
    }
  }

  @Test void isTraceTag()
  {
    if (Configuration.isTracingBuild())
    {
      assertTrue(Configuration.isTraceTag("theory::lemma"));
      assertFalse(Configuration.isTraceTag("theory::::lemma"));
    }
    else
    {
      assertFalse(Configuration.isTraceTag("theory::lemma"));
      assertFalse(Configuration.isTraceTag("theory::::lemma"));
    }
  }

  @Test void isGitBuild() {}

  @Test void getGitBranchName()
  {
    System.out.println(Configuration.getGitBranchName());
  }

  @Test void getGitCommit()
  {
    System.out.println(Configuration.getGitCommit());
  }

  @Test void hasGitModifications() {}

  @Test void getGitId()
  {
    System.out.println(Configuration.getGitId());
  }

  @Test void getCompiler()
  {
    System.out.println(Configuration.getCompiler());
  }

  @Test void getCompiledDateTime()
  {
    System.out.println(Configuration.getCompiledDateTime());
  }
}