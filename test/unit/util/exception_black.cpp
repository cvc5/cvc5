/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Exception.
 */

#include <iostream>
#include <sstream>

#include "base/exception.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackException : public TestInternal
{
};

// cvc5::Exception is a simple class, just test it all at once.
TEST_F(TestUtilBlackException, exceptions)
{
  Exception e1;
  Exception e2(std::string("foo!"));
  Exception e3("bar!");

  ASSERT_EQ(e1.toString(), std::string("Unknown exception"));
  ASSERT_EQ(e2.toString(), std::string("foo!"));
  ASSERT_EQ(e3.toString(), std::string("bar!"));

  e1.setMessage("blah");
  e2.setMessage("another");
  e3.setMessage("three of 'em!");

  std::stringstream s1, s2, s3;
  s1 << e1;
  s2 << e2;
  s3 << e3;

  ASSERT_EQ(s1.str(), std::string("blah"));
  ASSERT_EQ(s2.str(), std::string("another"));
  ASSERT_EQ(s3.str(), std::string("three of 'em!"));
}
}  // namespace test
}  // namespace cvc5::internal
