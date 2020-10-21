/*********************                                                        */
/*! \file theory_strings_word_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
    d_em = new ExprManager;
    d_smt = new SmtEngine(d_em, &opts);
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

    TypeNode stringType = d_nm->stringType();
    TS_ASSERT(Word::mkEmptyWord(stringType) == empty);

    std::vector<Node> vec;
    vec.push_back(abc);
    Node abcMk = Word::mkWordFlatten(vec);
    TS_ASSERT_EQUALS(abc, abcMk);
    vec.push_back(a);
    Node abcaMk = Word::mkWordFlatten(vec);
    TS_ASSERT_EQUALS(abca, abcaMk);

    TS_ASSERT(Word::getLength(empty) == 0);
    TS_ASSERT(Word::getLength(aaaaa) == 5);

    TS_ASSERT(Word::isEmpty(empty));
    TS_ASSERT(!Word::isEmpty(a));

    TS_ASSERT(Word::find(empty, empty) == 0);
    TS_ASSERT(Word::find(a, empty) == 0);
    TS_ASSERT(Word::find(empty, empty, 1) == std::string::npos);
    TS_ASSERT(Word::find(cac, a, 0) == 1);
    TS_ASSERT(Word::find(cac, abc) == std::string::npos);

    TS_ASSERT(Word::rfind(aaaaa, empty) == 0);
    TS_ASSERT(Word::rfind(aaaaa, a) == 0);
    TS_ASSERT(Word::rfind(abca, abc, 1) == 1);

    TS_ASSERT(Word::hasPrefix(empty, empty));
    TS_ASSERT(Word::hasPrefix(a, empty));
    TS_ASSERT(Word::hasPrefix(aaaaa, a));
    TS_ASSERT(!Word::hasPrefix(abca, b));
    TS_ASSERT(!Word::hasPrefix(empty, a));

    TS_ASSERT(Word::hasSuffix(empty, empty));
    TS_ASSERT(Word::hasSuffix(a, empty));
    TS_ASSERT(Word::hasSuffix(a, a));
    TS_ASSERT(!Word::hasSuffix(abca, b));
    TS_ASSERT(!Word::hasSuffix(empty, abc));

    TS_ASSERT_EQUALS(bbc, Word::replace(abc, a, b));
    TS_ASSERT_EQUALS(aaaaa, Word::replace(aaaaa, b, a));
    TS_ASSERT_EQUALS(aa, Word::replace(a, empty, a));

    TS_ASSERT_EQUALS(empty, Word::substr(a, 1));
    TS_ASSERT_EQUALS(empty, Word::substr(empty, 0));
    TS_ASSERT_EQUALS(a, Word::substr(abca, 3));

    TS_ASSERT_EQUALS(a, Word::substr(abc, 0, 1));
    TS_ASSERT_EQUALS(aa, Word::substr(aaaaa, 3, 2));

    TS_ASSERT_EQUALS(a, Word::prefix(a, 1));
    TS_ASSERT_EQUALS(empty, Word::prefix(empty, 0));
    TS_ASSERT_EQUALS(a, Word::prefix(aaaaa, 1));

    TS_ASSERT_EQUALS(a, Word::suffix(a, 1));
    TS_ASSERT_EQUALS(empty, Word::suffix(empty, 0));
    TS_ASSERT_EQUALS(aa, Word::suffix(aaaaa, 2));

    TS_ASSERT(!Word::noOverlapWith(abc, empty));
    TS_ASSERT(Word::noOverlapWith(cac, aa));
    TS_ASSERT(!Word::noOverlapWith(cac, abc));
    TS_ASSERT(Word::noOverlapWith(cac, b));
    TS_ASSERT(!Word::noOverlapWith(cac, a));
    TS_ASSERT(!Word::noOverlapWith(abca, a));

    TS_ASSERT(Word::overlap(abc, empty) == 0);
    TS_ASSERT(Word::overlap(aaaaa, abc) == 1);
    TS_ASSERT(Word::overlap(cac, abc) == 0);
    TS_ASSERT(Word::overlap(empty, abc) == 0);
    TS_ASSERT(Word::overlap(aaaaa, aa) == 2);

    TS_ASSERT(Word::roverlap(abc, empty) == 0);
    TS_ASSERT(Word::roverlap(aaaaa, abc) == 0);
    TS_ASSERT(Word::roverlap(cac, abc) == 1);
    TS_ASSERT(Word::roverlap(empty, abc) == 0);
    TS_ASSERT(Word::roverlap(aaaaa, aa) == 2);
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;

  NodeManager* d_nm;
};
