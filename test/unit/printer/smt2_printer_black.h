/*********************                                                        */
/*! \file smt2_printer_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the SMT2 printer
 **
 ** Black box testing of the SMT2 printer.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>

#include "api/cvc4cpp.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/language.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace CVC4::kind;

class Smt2PrinterBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_slv.reset(new api::Solver());
    d_nm = d_slv->getSmtEngine()->getNodeManager();
  }

  void tearDown() override { d_slv.reset(); }

  void checkToString(TNode n, const std::string& expected)
  {
    std::stringstream ss;
    ss << Node::setdepth(-1)
       << Node::setlanguage(language::output::LANG_SMTLIB_V2_6) << n;
    TS_ASSERT_EQUALS(ss.str(), expected);
  }

  void testRegexpRepeat()
  {
    Node n = d_nm->mkNode(
        d_nm->mkConst(RegExpRepeat(5)),
        d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("x"))));
    checkToString(n, "((_ re.^ 5) (str.to_re \"x\"))");
  }

  void testRegexpLoop()
  {
    Node n = d_nm->mkNode(
        d_nm->mkConst(RegExpLoop(1, 3)),
        d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("x"))));
    checkToString(n, "((_ re.loop 1 3) (str.to_re \"x\"))");
  }

 private:
  std::unique_ptr<api::Solver> d_slv;
  NodeManager* d_nm;
};
