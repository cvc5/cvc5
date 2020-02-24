/*********************                                                        */
/*! \file theory_strings_word_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for the strings word utilities
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/strings/word.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <memory>
#include <vector>

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

class TheoryStringsWordWhite : public CxxTest::TestSuite
{
 public:
  TheoryStringsWordWhite() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager(opts);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);

    d_nm = NodeManager::currentNM();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testStrings()
  {
    Node empty = d_nm->mkConst(String(""));
    Node a = d_nm->mkConst(String("a"));
    Node b = d_nm->mkConst(String("b"));
    Node aa = d_nm->mkConst(String("aa"));
    Node aaaaa = d_nm->mkConst(String("aaaaa"));
    Node abc = d_nm->mkConst(String("abc"));
    Node bbc = d_nm->mkConst(String("bbc"));
    Node cac = d_nm->mkConst(String("cac"));
    Node abca = d_nm->mkConst(String("abca"));

    TS_ASSERT(word::mkEmptyWord(kind::CONST_STRING) == empty);

    std::vector<Node> vec;
    vec.push_back(abc);
    Node abcMk = word::mkWord(vec);
    TS_ASSERT_EQUALS(abc, abcMk);
    vec.push_back(a);
    Node abcaMk = word::mkWord(vec);
    TS_ASSERT_EQUALS(abca, abcaMk);

    TS_ASSERT(word::getLength(empty) == 0);
    TS_ASSERT(word::getLength(aaaaa) == 5);

    TS_ASSERT(word::isEmpty(empty));
    TS_ASSERT(!word::isEmpty(a));

    TS_ASSERT(word::find(empty, empty) == 0);
    TS_ASSERT(word::find(a, empty) == 0);
    TS_ASSERT(word::find(empty, empty, 1) == std::string::npos);
    TS_ASSERT(word::find(cac, a, 0) == 1);
    TS_ASSERT(word::find(cac, abc) == std::string::npos);

    TS_ASSERT(word::rfind(aaaaa, empty) == 0);
    TS_ASSERT(word::rfind(aaaaa, a) == 0);
    TS_ASSERT(word::rfind(abca, abc, 1) == 1);

    TS_ASSERT(word::hasPrefix(empty, empty));
    TS_ASSERT(word::hasPrefix(a, empty));
    TS_ASSERT(word::hasPrefix(aaaaa, a));
    TS_ASSERT(!word::hasPrefix(abca, b));
    TS_ASSERT(!word::hasPrefix(empty, a));

    TS_ASSERT(word::hasSuffix(empty, empty));
    TS_ASSERT(word::hasSuffix(a, empty));
    TS_ASSERT(word::hasSuffix(a, a));
    TS_ASSERT(!word::hasSuffix(abca, b));
    TS_ASSERT(!word::hasSuffix(empty, abc));

    TS_ASSERT_EQUALS(bbc, word::replace(abc, a, b));
    TS_ASSERT_EQUALS(aaaaa, word::replace(aaaaa, b, a));
    TS_ASSERT_EQUALS(aa, word::replace(a, empty, a));

    TS_ASSERT_EQUALS(empty, word::substr(a, 1));
    TS_ASSERT_EQUALS(empty, word::substr(empty, 0));
    TS_ASSERT_EQUALS(a, word::substr(abca, 3));

    TS_ASSERT_EQUALS(a, word::substr(abc, 0, 1));
    TS_ASSERT_EQUALS(aa, word::substr(aaaaa, 3, 2));

    TS_ASSERT_EQUALS(a, word::prefix(a, 1));
    TS_ASSERT_EQUALS(empty, word::prefix(empty, 0));
    TS_ASSERT_EQUALS(a, word::prefix(aaaaa, 1));

    TS_ASSERT_EQUALS(a, word::suffix(a, 1));
    TS_ASSERT_EQUALS(empty, word::suffix(empty, 0));
    TS_ASSERT_EQUALS(aa, word::suffix(aaaaa, 2));

    TS_ASSERT(!word::noOverlapWith(abc, empty));
    TS_ASSERT(word::noOverlapWith(cac, aa));
    TS_ASSERT(!word::noOverlapWith(cac, abc));
    TS_ASSERT(word::noOverlapWith(cac, b));
    TS_ASSERT(!word::noOverlapWith(cac, a));
    TS_ASSERT(!word::noOverlapWith(abca, a));

    TS_ASSERT(word::overlap(abc, empty) == 0);
    TS_ASSERT(word::overlap(aaaaa, abc) == 1);
    TS_ASSERT(word::overlap(cac, abc) == 0);
    TS_ASSERT(word::overlap(empty, abc) == 0);
    TS_ASSERT(word::overlap(aaaaa, aa) == 2);

    TS_ASSERT(word::roverlap(abc, empty) == 0);
    TS_ASSERT(word::roverlap(aaaaa, abc) == 0);
    TS_ASSERT(word::roverlap(cac, abc) == 1);
    TS_ASSERT(word::roverlap(empty, abc) == 0);
    TS_ASSERT(word::roverlap(aaaaa, aa) == 2);
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;

  NodeManager* d_nm;
};
