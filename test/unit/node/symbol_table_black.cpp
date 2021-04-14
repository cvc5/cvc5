/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::SymbolTable.
 */

#include <sstream>
#include <string>

#include "base/check.h"
#include "base/exception.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/symbol_table.h"
#include "test_api.h"

namespace cvc5 {

using namespace kind;
using namespace context;

namespace test {

class TestNodeBlackSymbolTable : public TestApi
{
};

TEST_F(TestNodeBlackSymbolTable, bind1)
{
  SymbolTable symtab;
  api::Sort booleanType = d_solver.getBooleanSort();
  api::Term x = d_solver.mkConst(booleanType);
  symtab.bind("x", x);
  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), x);
}

TEST_F(TestNodeBlackSymbolTable, bind2)
{
  SymbolTable symtab;
  api::Sort booleanType = d_solver.getBooleanSort();
  // var name attribute shouldn't matter
  api::Term y = d_solver.mkConst(booleanType, "y");
  symtab.bind("x", y);
  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), y);
}

TEST_F(TestNodeBlackSymbolTable, bind3)
{
  SymbolTable symtab;
  api::Sort booleanType = d_solver.getBooleanSort();
  api::Term x = d_solver.mkConst(booleanType);
  symtab.bind("x", x);
  api::Term y = d_solver.mkConst(booleanType);
  // new binding covers old
  symtab.bind("x", y);
  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), y);
}

TEST_F(TestNodeBlackSymbolTable, bind4)
{
  SymbolTable symtab;
  api::Sort booleanType = d_solver.getBooleanSort();
  api::Term x = d_solver.mkConst(booleanType);
  symtab.bind("x", x);

  api::Sort t = d_solver.mkUninterpretedSort("T");
  // duplicate binding for type is OK
  symtab.bindType("x", t);

  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), x);
  ASSERT_TRUE(symtab.isBoundType("x"));
  ASSERT_EQ(symtab.lookupType("x"), t);
}

TEST_F(TestNodeBlackSymbolTable, bind_type1)
{
  SymbolTable symtab;
  api::Sort s = d_solver.mkUninterpretedSort("S");
  symtab.bindType("S", s);
  ASSERT_TRUE(symtab.isBoundType("S"));
  ASSERT_EQ(symtab.lookupType("S"), s);
}

TEST_F(TestNodeBlackSymbolTable, bind_type2)
{
  SymbolTable symtab;
  // type name attribute shouldn't matter
  api::Sort s = d_solver.mkUninterpretedSort("S");
  symtab.bindType("T", s);
  ASSERT_TRUE(symtab.isBoundType("T"));
  ASSERT_EQ(symtab.lookupType("T"), s);
}

TEST_F(TestNodeBlackSymbolTable, bind_type3)
{
  SymbolTable symtab;
  api::Sort s = d_solver.mkUninterpretedSort("S");
  symtab.bindType("S", s);
  api::Sort t = d_solver.mkUninterpretedSort("T");
  // new binding covers old
  symtab.bindType("S", t);
  ASSERT_TRUE(symtab.isBoundType("S"));
  ASSERT_EQ(symtab.lookupType("S"), t);
}

TEST_F(TestNodeBlackSymbolTable, push_scope)
{
  SymbolTable symtab;
  api::Sort booleanType = d_solver.getBooleanSort();
  api::Term x = d_solver.mkConst(booleanType);
  symtab.bind("x", x);
  symtab.pushScope();

  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), x);

  api::Term y = d_solver.mkConst(booleanType);
  symtab.bind("x", y);

  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), y);

  symtab.popScope();
  ASSERT_TRUE(symtab.isBound("x"));
  ASSERT_EQ(symtab.lookup("x"), x);
}

TEST_F(TestNodeBlackSymbolTable, bad_pop)
{
  SymbolTable symtab;
  ASSERT_THROW(symtab.popScope(), ScopeException);
}

}  // namespace test
}  // namespace cvc5
