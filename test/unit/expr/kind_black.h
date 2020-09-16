/*********************                                                        */
/*! \file kind_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Kind.
 **
 ** Black box testing of CVC4::Kind.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <string>
#include <sstream>

#include "expr/kind.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class KindBlack : public CxxTest::TestSuite {
  Kind undefined;
  Kind null;
  Kind last;
  
  //easier to define in setup
  int beyond;
  Kind unknown;

 public:
  void setUp() override
  {
    undefined = UNDEFINED_KIND;
    null = NULL_EXPR;
    last = LAST_KIND;
    beyond = ((int)LAST_KIND) + 1;
    unknown = (Kind)beyond;
  }

  
  void testEquality(){

    TS_ASSERT_EQUALS(undefined, UNDEFINED_KIND);
    TS_ASSERT_EQUALS(last, LAST_KIND);
  }
  
  void testOrder(){
    TS_ASSERT_LESS_THAN(int(undefined), int(null));
    TS_ASSERT_LESS_THAN(int(null), int(last));
    TS_ASSERT_LESS_THAN(int(undefined), int(last));
    TS_ASSERT_LESS_THAN(int(last), int(unknown));
  }

  bool stringIsAsExpected(Kind k, const char * s){
    stringstream act;
    stringstream exp;

    act << k;
    exp << s;
    
    string actCreated = act.str();
    string expCreated = exp.str();
    return actCreated == expCreated;
  }

  void testOperatorLtLt() {

    TS_ASSERT(stringIsAsExpected(undefined, "UNDEFINED_KIND"));
    TS_ASSERT(stringIsAsExpected(null, "NULL"));
    TS_ASSERT(stringIsAsExpected(last, "LAST_KIND"));    

  }
  void testOperatorLtLtConcat() {

    stringstream act, exp;
    act << undefined << null << last << unknown;
    exp << "UNDEFINED_KIND" << "NULL" << "LAST_KIND" << "?";
    
    string actCreated = act.str();
    string expCreated = exp.str();
    
    TS_ASSERT_EQUALS(actCreated, expCreated);
  }

};
