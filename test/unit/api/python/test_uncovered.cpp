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
 * Testing stuff that is not exposed by the python API to fix code coverage
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

    std::stringstream ss;
    {
        auto info = d_solver.getOptionInfo("verbose");
        ss << info;
    }
    {
        auto info = d_solver.getOptionInfo("print-success");
        ss << info;
        info.boolValue();
    }
    {
        auto info = d_solver.getOptionInfo("verbosity");
        ss << info;
        info.intValue();
    }
    {
        auto info = d_solver.getOptionInfo("rlimit");
        ss << info;
        info.uintValue();
    }
    {
        auto info = d_solver.getOptionInfo("random-freq");
        ss << info;
        info.doubleValue();
    }
    {
        auto info = d_solver.getOptionInfo("force-logic");
        ss << info;
        info.stringValue();
    }
    {
        auto info = d_solver.getOptionInfo("simplification");
        ss << info;
    }
}

TEST_F(TestApiBlackUncovered, Statistics)
{
    d_solver.assertFormula(d_solver.mkConst(d_solver.getBooleanSort(), "x"));
    d_solver.checkSat();
    Statistics stats = d_solver.getStatistics();
    std::stringstream ss;
    ss << stats;
    auto it = stats.begin();
    ASSERT_NE(it, stats.end());
    it++;
    it--;
    ++it;
    --it;
    ASSERT_EQ(it, stats.begin());
    ss << it->first;

}

}  // namespace test
}  // namespace cvc5::internal
