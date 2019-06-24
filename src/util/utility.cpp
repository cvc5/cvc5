/*********************                                                        */
/*! \file utility.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Some standard STL-related utility functions for CVC4
 **
 ** Some standard STL-related utility functions for CVC4.
 **/

#include "util/utility.h"

#include <unistd.h>

#include <cstdlib>
#include <iostream>

#include "base/cvc4_check.h"

namespace CVC4 {

std::fstream openTmpFile(std::string* pattern)
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
    CVC4_FATAL() << "Could not create temporary file " << *pattern;
  }
  std::fstream tmpStream(tmpName);
  close(r);
  *pattern = std::string(tmpName);
  delete[] tmpName;
  return tmpStream;
}

}  // namespace CVC4
