/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Testing stuff that is not exposed by the Java API to fix code coverage
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackUncovered : public TestApi
{
};

TEST_F(TestApiBlackUncovered, streaming_operators)
{
    std::stringstream ss;
    ss << cvc5::modes::LearnedLitType::PREPROCESS;
    ss << cvc5::SynthResult();
}

TEST_F(TestApiBlackUncovered, Options)
{
    auto dopts = d_solver.getDriverOptions();
    dopts.err();
    dopts.in();
    dopts.out();
}

TEST_F(TestApiBlackUncovered, Statistics)
{
    Stat stat;
    stat = Stat();
    Statistics stats = d_solver.getStatistics();
    auto it = stats.begin();
    it++;
    it--;
    ++it;
    --it;
}

}  // namespace test
}  // namespace cvc5::internal
