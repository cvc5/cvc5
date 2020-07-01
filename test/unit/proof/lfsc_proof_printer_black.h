/*********************                                                        */
/*! \file lfsc_proof_printer_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of LFSC proof printing
 **/

#include <cxxtest/TestSuite.h>

#include "proof/lfsc_proof_printer.h"
#include "prop/sat_solver_types.h"
#include "proof/clause_id.h"

using namespace CVC4::proof;
using namespace CVC4::prop;

class LfscProofPrinterBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testPrintClause();
  void testPrintSatInputProof();
  void testPrintCMapProof();
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

void LfscProofPrinterBlack::testPrintSatInputProof()
{
  std::vector<CVC4::ClauseId> ids{2, 40, 3};
  std::ostringstream lfsc;

  LFSCProofPrinter::printSatInputProof(ids, lfsc, "");

  std::string expectedLfsc =
      "(cnfc_proof _ _ _ .pb2 "
      "(cnfc_proof _ _ _ .pb40 "
      "(cnfc_proof _ _ _ .pb3 "
      "cnfn_proof)))";

  std::ostringstream lfscWithoutWhitespace;
  for (char c : lfsc.str())
  {
    if (!std::isspace(c))
    {
      lfscWithoutWhitespace << c;
    }
  }
  std::ostringstream expectedLfscWithoutWhitespace;
  for (char c : expectedLfsc)
  {
    if (!std::isspace(c))
    {
      expectedLfscWithoutWhitespace << c;
    }
  }

  TS_ASSERT_EQUALS(lfscWithoutWhitespace.str(),
                   expectedLfscWithoutWhitespace.str());
}

void LfscProofPrinterBlack::testPrintCMapProof()
{
  std::vector<CVC4::ClauseId> ids{2, 40, 3};
  std::ostringstream lfsc;

  LFSCProofPrinter::printCMapProof(ids, lfsc, "");

  std::string expectedLfsc =
      "(CMapc_proof 1 _ _ _ .pb2 "
      "(CMapc_proof 2 _ _ _ .pb40 "
      "(CMapc_proof 3 _ _ _ .pb3 "
      "CMapn_proof)))";

  std::ostringstream lfscWithoutWhitespace;
  for (char c : lfsc.str())
  {
    if (!std::isspace(c))
    {
      lfscWithoutWhitespace << c;
    }
  }
  std::ostringstream expectedLfscWithoutWhitespace;
  for (char c : expectedLfsc)
  {
    if (!std::isspace(c))
    {
      expectedLfscWithoutWhitespace << c;
    }
  }

  TS_ASSERT_EQUALS(lfscWithoutWhitespace.str(),
                   expectedLfscWithoutWhitespace.str());
}
