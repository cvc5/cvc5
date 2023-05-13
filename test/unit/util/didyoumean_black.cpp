/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Stat and associated classes.
 */

#include "test.h"

#include "util/didyoumean.h"

namespace cvc5::internal::test {

class TestUtilDidYouMean : public TestInternal
{
};

TEST_F(TestUtilDidYouMean, getMatch)
{
  {
    DidYouMean dym;
    dym.addWords({"abfish", "cdfish", "whale"});
    {
      auto expected = std::vector<std::string>{"abfish"};
      EXPECT_EQ(dym.getMatch("abfish"), expected);
    }
    {
      auto expected = std::vector<std::string>{"whale"};
      EXPECT_EQ(dym.getMatch("wahl"), expected);
    }
    {
      auto expected = std::vector<std::string>{"abfish", "cdfish"};
      EXPECT_EQ(dym.getMatch("fish"), expected);
    }
    {
      auto expected = std::vector<std::string>{};
      EXPECT_EQ(dym.getMatch("elephant"), expected);
    }
  }
}

TEST_F(TestUtilDidYouMean, getMatchAsString)
{
    DidYouMean dym;
    dym.addWords({"abfish", "cdfish", "whale"});
    {
      std::string expected = "";
      EXPECT_EQ(dym.getMatchAsString("elephant"), expected);
    }
    {
      std::string expected = R"FOOBAR(

Did you mean this?
        whale)FOOBAR";
      EXPECT_EQ(dym.getMatchAsString("wahl"), expected);
    }
    {
      std::string expected = R"FOOBAR(

Did you mean any of these?
        abfish
        cdfish)FOOBAR";
      EXPECT_EQ(dym.getMatchAsString("fish"), expected);
    }
}

}  // namespace cvc5::internal::test
