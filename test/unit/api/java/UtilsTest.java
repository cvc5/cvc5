/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of Utils JAR extraction helpers.
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.Utils;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FilterInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import org.junit.jupiter.api.Test;

class UtilsTest
{
  private static final class TrackingInputStream extends FilterInputStream
  {
    boolean closed = false;

    TrackingInputStream(InputStream in)
    {
      super(in);
    }

    @Override
    public void close() throws IOException
    {
      closed = true;
      super.close();
    }
  }

  @Test
  void extractToFileClosesInputOnSuccess() throws Exception
  {
    byte[] payload = new byte[] {1, 2, 3, 4};
    TrackingInputStream in = new TrackingInputStream(new ByteArrayInputStream(payload));
    File dest = Files.createTempFile("cvc5-extract", ".bin").toFile();
    dest.deleteOnExit();

    Utils.extractToFile(in, dest);

    assertTrue(in.closed);
    assertArrayEquals(payload, Files.readAllBytes(dest.toPath()));
  }

  @Test
  void extractToFileClosesInputWhenDestCannotBeOpened() throws Exception
  {
    TrackingInputStream in = new TrackingInputStream(new ByteArrayInputStream(new byte[] {1}));
    File dest = Files.createTempDirectory("cvc5-extract").toFile();
    try
    {
      assertThrows(IOException.class, () -> Utils.extractToFile(in, dest));
      assertTrue(in.closed);
    }
    finally
    {
      dest.delete();
    }
  }
}
