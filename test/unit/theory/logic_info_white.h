/*********************                                                        */
/*! \file logic_info_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009--2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Unit testing for CVC4::LogicInfo class
 **
 ** Unit testing for CVC4::LogicInfo class.
 **/

#include <cxxtest/TestSuite.h>

#include "expr/kind.h"
#include "theory/logic_info.h"

using namespace CVC4;
using namespace CVC4::theory;

using namespace std;

class LogicInfoWhite : public CxxTest::TestSuite {

public:

  void testSmtlibLogics() {
    LogicInfo info("QF_SAT");
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isQuantified() );

    info = LogicInfo("AUFLIA");
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("AUFLIRA");
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("AUFNIRA");
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("LRA");
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("QF_ABV");
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info = LogicInfo("QF_AUFBV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info = LogicInfo("QF_AUFLIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_AX");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info = LogicInfo("QF_BV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info = LogicInfo("QF_IDL");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_LIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_LRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("QF_NIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_NRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("QF_RDL");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("QF_UF");
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info = LogicInfo("QF_UFBV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info = LogicInfo("QF_UFIDL");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_UFLIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_UFLRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("QF_UFNRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("UFLRA");
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("UFNIA");
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info = LogicInfo("QF_ALL_SUPPORTED");
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info = LogicInfo("ALL_SUPPORTED");
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );
  }

  void testDefaultLogic() {
    LogicInfo info;
    TS_ASSERT( !info.isLocked() );

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( info.getLogicString(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_BUILTIN ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_BOOL ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_UF ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_ARITH ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_ARRAY ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_BV ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_DATATYPES ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_QUANTIFIERS ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isTheoryEnabled( THEORY_REWRITERULES ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_BUILTIN ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_BOOL ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_UF ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_ARITH ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_ARRAY ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_BV ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_DATATYPES ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_QUANTIFIERS ), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isPure( THEORY_REWRITERULES ), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.isQuantified(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.areIntegersUsed(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.areRealsUsed(), CVC4::AssertionException );
    TS_ASSERT_THROWS( ! info.isLinear(), CVC4::AssertionException );
#endif /* CVC4_ASSERTIONS */

    info.lock();
    TS_ASSERT( info.isLocked() );
    TS_ASSERT_EQUALS( info.getLogicString(), "AUFBVDTNIRA" );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BUILTIN ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_QUANTIFIERS ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_REWRITERULES ) );
    TS_ASSERT( ! info.isPure( THEORY_BUILTIN ) );
    TS_ASSERT( ! info.isPure( THEORY_BOOL ) );
    TS_ASSERT( ! info.isPure( THEORY_UF ) );
    TS_ASSERT( ! info.isPure( THEORY_ARITH ) );
    TS_ASSERT( ! info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( ! info.isPure( THEORY_BV ) );
    TS_ASSERT( ! info.isPure( THEORY_DATATYPES ) );
    TS_ASSERT( ! info.isPure( THEORY_QUANTIFIERS ) );
    TS_ASSERT( ! info.isPure( THEORY_REWRITERULES ) );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );
    TS_ASSERT( ! info.isLinear() );

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( info.arithOnlyLinear(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableIntegers(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableQuantifiers(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableTheory(THEORY_BV), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableTheory(THEORY_DATATYPES), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.enableIntegers(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableReals(), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableTheory(THEORY_ARITH), CVC4::AssertionException );
    TS_ASSERT_THROWS( info.disableTheory(THEORY_UF), CVC4::AssertionException );
#endif /* CVC4_ASSERTIONS */

    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.arithOnlyLinear();
    info.disableIntegers();
    info.lock();
    TS_ASSERT_EQUALS( info.getLogicString(), "AUFBVDTLRA" );

    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.disableQuantifiers();
    info.lock();
    TS_ASSERT_EQUALS( info.getLogicString(), "QF_AUFBVDTLRA" );

    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.disableTheory(THEORY_BV);
    info.disableTheory(THEORY_DATATYPES);
    info.enableIntegers();
    info.disableReals();
    info.lock();
    TS_ASSERT_EQUALS( info.getLogicString(), "QF_AUFLIA" );

    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.disableTheory(THEORY_ARITH);
    info.disableTheory(THEORY_UF);
    info.lock();
    TS_ASSERT_EQUALS( info.getLogicString(), "QF_AX" );
    TS_ASSERT( info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( ! info.isQuantified() );

    // check all-excluded logic
    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.disableEverything();
    info.lock();
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areRealsUsed() );

    // check copy is unchanged
    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.lock();
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areRealsUsed() );

    // check all-included logic
    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.enableEverything();
    info.lock();
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    // check copy is unchanged
    info = info.getUnlockedCopy();
    TS_ASSERT( !info.isLocked() );
    info.lock();
    TS_ASSERT( info.isLocked() );
    TS_ASSERT( !info.isPure( THEORY_BOOL ) );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_DATATYPES ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );
  }

};/* class LogicInfoWhite */

