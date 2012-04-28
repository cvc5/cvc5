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
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( info.isPure( THEORY_BOOL ) );
    TS_ASSERT( !info.isQuantified() );

    info.setLogicString("AUFLIA");
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("AUFLIRA");
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("AUFNIRA");
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("LRA");
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("QF_ABV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info.setLogicString("QF_AUFBV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info.setLogicString("QF_AUFLIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("QF_AX");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info.setLogicString("QF_BV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info.setLogicString("QF_IDL");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("QF_LIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("QF_LRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("QF_NIA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("QF_NRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("QF_RDL");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("QF_UF");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( !info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( info.isPure( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info.setLogicString("QF_UFBV");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );

    info.setLogicString("QF_UFIDL");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( info.isLinear() );
    TS_ASSERT( info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("QF_UFLIA");
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
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );

    info.setLogicString("QF_UFLRA");
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

    info.setLogicString("QF_UFNRA");
    TS_ASSERT( !info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( !info.areIntegersUsed() );
    TS_ASSERT( info.areRealsUsed() );

    info.setLogicString("UFLRA");
    TS_ASSERT( info.isQuantified() );
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

    info.setLogicString("UFNIA");
    TS_ASSERT( info.isQuantified() );
    TS_ASSERT( info.isSharingEnabled() );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_ARRAY ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_UF ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_ARITH ) );
    TS_ASSERT( !info.isPure( THEORY_ARITH ) );
    TS_ASSERT( !info.isTheoryEnabled( THEORY_BV ) );
    TS_ASSERT( info.isTheoryEnabled( THEORY_BOOL ) );
    TS_ASSERT( !info.isLinear() );
    TS_ASSERT( !info.isDifferenceLogic() );
    TS_ASSERT( info.areIntegersUsed() );
    TS_ASSERT( !info.areRealsUsed() );
  }

  void testDefaultLogic() {
    LogicInfo info;
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

    info.arithOnlyLinear();
    info.disableIntegers();
    TS_ASSERT_EQUALS( info.getLogicString(), "AUFBVDTLRA" );
    info.disableQuantifiers();
    TS_ASSERT_EQUALS( info.getLogicString(), "QF_AUFBVDTLRA" );
    info.disableTheory(THEORY_BV);
    info.disableTheory(THEORY_DATATYPES);
    info.enableIntegers();
    info.disableReals();
    TS_ASSERT_EQUALS( info.getLogicString(), "QF_AUFLIA" );
    info.disableTheory(THEORY_ARITH);
    info.disableTheory(THEORY_UF);
    TS_ASSERT_EQUALS( info.getLogicString(), "QF_AX" );
    TS_ASSERT( info.isPure( THEORY_ARRAY ) );
    TS_ASSERT( ! info.isQuantified() );
  }

};/* class LogicInfoWhite */

