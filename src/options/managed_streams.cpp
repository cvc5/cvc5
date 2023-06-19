/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrappers to handle memory management of streams.
 *
 * This file contains wrappers to handle special cases of managing memory
 * related to streams stored in options.
 */

#include "options/managed_streams.h"

#include <string.h>

#include <cerrno>
#include <fstream>
#include <iostream>
#include <sstream>

#include "options/option_exception.h"

namespace cvc5::internal {

std::string cvc5_errno_failreason()
{
#if HAVE_STRERROR_R
#if STRERROR_R_CHAR_P
  if (errno != 0)
  {
    // GNU version of strerror_r: *might* use the given buffer,
    // or might not.  It returns a pointer to buf, or not.
    char buf[80];
    return std::string(strerror_r(errno, buf, sizeof buf));
  }
  else
  {
    return "unknown reason";
  }
#else  /* STRERROR_R_CHAR_P */
  if (errno != 0)
  {
    // XSI version of strerror_r: always uses the given buffer.
    // Returns an error code.
    char buf[80];
    if (strerror_r(errno, buf, sizeof buf) == 0)
    {
      return std::string(buf);
    }
    else
    {
      // some error occurred while getting the error string
      return "unknown reason";
    }
  }
  else
  {
    return "unknown reason";
  }
#endif /* STRERROR_R_CHAR_P */
#else  /* HAVE_STRERROR_R */
  return "unknown reason";
#endif /* HAVE_STRERROR_R */
}

namespace detail {

std::unique_ptr<std::ostream> openOStream(const std::string& filename)
{
  errno = 0;
  std::unique_ptr<std::ostream> res = std::make_unique<std::ofstream>(filename);
  if (!res || !*res)
  {
    std::stringstream ss;
    ss << "Cannot open file: `" << filename << "': " << cvc5_errno_failreason();
    throw OptionException(ss.str());
  }
  return res;
}
std::unique_ptr<std::istream> openIStream(const std::string& filename)
{
  errno = 0;
  std::unique_ptr<std::istream> res = std::make_unique<std::ifstream>(filename);
  if (!res || !*res)
  {
    std::stringstream ss;
    ss << "Cannot open file: `" << filename << "': " << cvc5_errno_failreason();
    throw OptionException(ss.str());
  }
  return res;
}
}  // namespace detail

ManagedErr::ManagedErr() : ManagedStream(&std::cerr, "stderr") {}
bool ManagedErr::specialCases(const std::string& value)
{
  if (value == "stderr" || value == "--")
  {
    d_nonowned = &std::cerr;
    d_owned.reset();
    d_description = "stderr";
    return true;
  }
  else if (value == "stdout")
  {
    d_nonowned = &std::cout;
    d_owned.reset();
    d_description = "stdout";
    return true;
  }
  return false;
}

ManagedIn::ManagedIn() : ManagedStream(&std::cin, "stdin") {}
bool ManagedIn::specialCases(const std::string& value)
{
  if (value == "stdin" || value == "--")
  {
    d_nonowned = &std::cin;
    d_owned.reset();
    d_description = "stdin";
    return true;
  }
  return false;
}

ManagedOut::ManagedOut() : ManagedStream(&std::cout, "stdout") {}
bool ManagedOut::specialCases(const std::string& value)
{
  if (value == "stdout" || value == "--")
  {
    d_nonowned = &std::cout;
    d_owned.reset();
    d_description = "stdout";
    return true;
  }
  else if (value == "stderr")
  {
    d_nonowned = &std::cerr;
    d_owned.reset();
    d_description = "stderr";
    return true;
  }
  return false;
}

}  // namespace cvc5::internal
