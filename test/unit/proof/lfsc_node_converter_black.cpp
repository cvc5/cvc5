/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of LFSC proof conversion
 */

#include <string>

#include "proof/lfsc/lfsc_node_converter.h"
#include "test.h"

namespace cvc5::internal {
using namespace cvc5::internal::proof;

namespace test {

class TestLfscNodeConverterBlack : public TestInternal
{
};

TEST_F(TestLfscNodeConverterBlack, ident_sanitize)
{
  // LFSC does not allow these characters in identifier bodies: "() \t\n\f;"
  //
  // See also: https://github.com/cvc5/LFSC/blob/master/src/lexer.flex#L24
  //
  // We use hex escapes that are valid in Python:
  // https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there are spaces"),
            R"x(cvc.there\x20are\x20spaces)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("  "), R"x(cvc.\x20\x20)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there\\are\\slashes"),
            R"x(cvc.there\x5care\x5cslashes)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there\nare\nnewlines"),
            R"x(cvc.there\x0aare\x0anewlines)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there\rare\rCRs"),
            "cvc.there\rare\rCRs");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there\tare\ttabs"),
            R"x(cvc.there\x09are\x09tabs)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there(are(parens"),
            R"x(cvc.there\x28are\x28parens)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there)are)parens"),
            R"x(cvc.there\x29are\x29parens)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName("there;are;semis"),
            R"x(cvc.there\x3bare\x3bsemis)x");
  ASSERT_EQ(LfscNodeConverter::getNameForUserName(""), R"x(cvc.)x");
}

}  // namespace test

}  // namespace cvc5::internal
