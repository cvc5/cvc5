/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Some standard STL-related utility functions for cvc5.
 */

#include "util/utility.h"

#include <unistd.h>

#include <cstdlib>

#include "base/check.h"

namespace cvc5::internal {

std::unique_ptr<std::fstream> openTmpFile(std::string* pattern)
{
  char* tmpDir = getenv("TMPDIR");
  if (tmpDir != nullptr)
  {
    *pattern = std::string(tmpDir) + "/" + *pattern;
  }
  else
  {
    *pattern = "/tmp/" + *pattern;
  }

  // Note: With C++17, we can avoid creating a copy using std::string::data().
  char* tmpName = new char[pattern->size() + 1];
  pattern->copy(tmpName, pattern->size());
  tmpName[pattern->size()] = '\0';
  int r = mkstemp(tmpName);
  if (r == -1)
  {
    CVC5_FATAL() << "Could not create temporary file " << *pattern;
  }
  std::unique_ptr<std::fstream> tmpStream(new std::fstream(tmpName));
  close(r);
  *pattern = std::string(tmpName);
  delete[] tmpName;
  return tmpStream;
}

}  // namespace cvc5::internal
