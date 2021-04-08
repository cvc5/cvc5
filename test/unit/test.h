/*********************                                                        */
/*! \file test.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common header for API unit test.
 **/

#ifndef CVC4__TEST__UNIT__TEST_H
#define CVC4__TEST__UNIT__TEST_H

#include "gtest/gtest.h"

namespace cvc5 {
namespace test {

class TestInternal : public ::testing::Test
{
};

}  // namespace test
}  // namespace cvc5
#endif
