/*********************                                                        */
/*! \file strings_rewriter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for the strings rewriter
 **
 ** Unit tests for the strings rewriter.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"
#include "theory/strings/strings_rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

class StringsRewriterWhite : public CxxTest::TestSuite
{
 public:
  StringsRewriterWhite() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager;
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_nm, &opts);
    d_scope = new SmtScope(d_smt);
    d_smt->finishInit();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testRewriteLeq()
  {
    TypeNode intType = d_nm->integerType();
    TypeNode strType = d_nm->stringType();

    Node a = d_nm->mkConst(::CVC4::String("A"));
    Node bc = d_nm->mkConst(::CVC4::String("BC"));
    Node x = d_nm->mkVar("x", strType);
    Node y = d_nm->mkVar("y", strType);

    Node ax = d_nm->mkNode(STRING_CONCAT, a, x);
    Node bcy = d_nm->mkNode(STRING_CONCAT, bc, y);

    {
      Node leq = d_nm->mkNode(STRING_LEQ, ax, bcy);
      TS_ASSERT_EQUALS(Rewriter::rewrite(leq), d_nm->mkConst(true));
    }

    {
      Node leq = d_nm->mkNode(STRING_LEQ, bcy, ax);
      TS_ASSERT_EQUALS(Rewriter::rewrite(leq), d_nm->mkConst(false));
    }
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;

  NodeManager* d_nm;
};
