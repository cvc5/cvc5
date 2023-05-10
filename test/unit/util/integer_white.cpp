/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::Integer.
 */

#include <sstream>

#include "test.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace test {

class TestUtilWhiteInteger : public TestInternal
{
 protected:
  static const char* s_large_val;
};

const char* TestUtilWhiteInteger::s_large_val =
    "4547897890548754897897897897890789078907890";

TEST_F(TestUtilWhiteInteger, hash)
{
  Integer large(s_large_val);
  Integer zero;
  Integer fits_in_2_bytes(55890);
  Integer fits_in_16_bytes("7890D789D33234027890D789D3323402", 16);

  ASSERT_NO_THROW(zero.hash());
  ASSERT_NO_THROW(fits_in_2_bytes.hash());
  ASSERT_NO_THROW(fits_in_16_bytes.hash());
  ASSERT_NO_THROW(large.hash());
}

/** Make sure we can handle: http://www.ginac.de/CLN/cln_3.html#SEC15 */
TEST_F(TestUtilWhiteInteger, construction)
{
  const int32_t i = (1 << 29) + 1;
  const uint32_t u = (1 << 29) + 1;
  ASSERT_EQ(Integer(i), Integer(i));
  ASSERT_EQ(Integer(u), Integer(u));
}
}  // namespace test
}  // namespace cvc5::internal
