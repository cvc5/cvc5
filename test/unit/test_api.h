/*********************                                                        */
/*! \file test_api.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common header for API unit test.
 **/

#ifndef CVC4__TEST__UNIT__TEST_API_H
#define CVC4__TEST__UNIT__TEST_API_H

#include "api/cvc4cpp.h"
#include "gtest/gtest.h"

namespace CVC4 {
namespace test {

class TestApi : public ::testing::Test
{
 protected:
  CVC4::api::Solver d_solver;
};

}  // namespace test
}  // namespace CVC4
#endif
