/*********************                                                        */
/*! \file lfsc_proof_printer_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of LFSC proof printing
 **/

#include <cxxtest/TestSuite.h>

#include "proof/lfsc_proof_printer.h"
#include "prop/sat_solver_types.h"

using namespace CVC4::proof;
using namespace CVC4::prop;

class LfscProofPrinterBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testPrintClause();
};

void LfscProofPrinterBlack::testPrintClause()
{
  SatClause clause{
      SatLiteral(0, false), SatLiteral(1, true), SatLiteral(3, false)};
  std::ostringstream lfsc;

  LFSCProofPrinter::printSatClause(clause, lfsc, "");

  std::string expectedLfsc =
      "(clc (pos .v0) "
      "(clc (neg .v1) "
      "(clc (pos .v3) "
      "cln)))";

  TS_ASSERT_EQUALS(lfsc.str(), expectedLfsc);
}
