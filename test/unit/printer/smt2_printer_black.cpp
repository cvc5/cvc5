/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SMT2 printer.
 */

#include <cvc5/cvc5.h>

#include <iostream>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/language.h"
#include "smt/solver_engine.h"
#include "test_smt.h"
#include "util/regexp.h"
#include "util/string.h"

namespace cvc5::internal {

using namespace kind;

namespace test {

class TestPrinterBlackSmt2 : public TestSmt
{
 protected:
  void checkToString(TNode n, const std::string& expected)
  {
    std::stringstream ss;
    options::ioutils::applyNodeDepth(ss, -1);
    options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
    ss << n;
    ASSERT_EQ(ss.str(), expected);
  }
};

TEST_F(TestPrinterBlackSmt2, regexp_repeat)
{
  Node n = d_nodeManager->mkNode(
      d_nodeManager->mkConst(RegExpRepeat(5)),
      d_nodeManager->mkNode(STRING_TO_REGEXP,
                            d_nodeManager->mkConst(String("x"))));
  checkToString(n, "((_ re.^ 5) (str.to_re \"x\"))");
}

TEST_F(TestPrinterBlackSmt2, regexp_loop)
{
  Node n = d_nodeManager->mkNode(
      d_nodeManager->mkConst(RegExpLoop(1, 3)),
      d_nodeManager->mkNode(STRING_TO_REGEXP,
                            d_nodeManager->mkConst(String("x"))));
  checkToString(n, "((_ re.loop 1 3) (str.to_re \"x\"))");
}
}  // namespace test
}  // namespace cvc5::internal
