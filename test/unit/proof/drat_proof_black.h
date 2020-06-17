/*********************                                                        */
/*! \file drat_proof_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the DRAT proof class
 **
 ** In particular, tests DRAT binary parsing.
 **/

#include <cxxtest/TestSuite.h>

#include <cctype>

#include "proof/drat/drat_proof.h"

using namespace CVC4::proof::drat;

class DratProofBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testParseOneAdd();
  void testParseOneMediumAdd();
  void testParseOneBigAdd();
  void testParseLiteralIsTooBig();
  void testParseLiteralOverflow();
  void testParseClauseOverflow();

  void testParseTwo();

  void testOutputTwoAsText();
  void testOutputTwoAsLfsc();
};

void DratProofBlack::testParseOneAdd()
{
  // a 1;
  std::string input("a\x02\x00", 3);
  DratProof proof = DratProof::fromBinary(input);

  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_kind, ADDITION);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause.size(), 1);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause[0],
                   SatLiteral(0, false));
}

void DratProofBlack::testParseOneMediumAdd()
{
  // a -255;
  std::string input("a\xff\x01\x00", 4);
  DratProof proof = DratProof::fromBinary(input);

  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_kind, ADDITION);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause.size(), 1);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause[0],
                   SatLiteral(126, true));
}

void DratProofBlack::testParseOneBigAdd()
{
  // a -2199023255551;
  std::string input("a\xff\xff\xff\xff\xff\x7f\x00", 8);
  DratProof proof = DratProof::fromBinary(input);

  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_kind, ADDITION);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause.size(), 1);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause[0],
                   SatLiteral(2199023255550, true));
}

void DratProofBlack::testParseLiteralIsTooBig()
{
  std::string input("a\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x00",
                    14);
  TS_ASSERT_THROWS(DratProof::fromBinary(input), InvalidDratProofException&);
}

void DratProofBlack::testParseLiteralOverflow()
{
  std::string input("a\x80", 2);
  TS_ASSERT_THROWS(DratProof::fromBinary(input), InvalidDratProofException&);
}

void DratProofBlack::testParseClauseOverflow()
{
  std::string input("a\x80\x01", 3);
  TS_ASSERT_THROWS(DratProof::fromBinary(input), InvalidDratProofException&);
}

void DratProofBlack::testParseTwo()
{
  // d -63 -8193
  // 129 -8191
  std::string input("\x64\x7f\x83\x80\x01\x00\x61\x82\x02\xff\x7f\x00", 12);
  DratProof proof = DratProof::fromBinary(input);

  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_kind, DELETION);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause.size(), 2);
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause[0],
                   SatLiteral(62, true));
  TS_ASSERT_EQUALS(proof.getInstructions()[0].d_clause[1],
                   SatLiteral(8192, true));

  TS_ASSERT_EQUALS(proof.getInstructions()[1].d_kind, ADDITION);
  TS_ASSERT_EQUALS(proof.getInstructions()[1].d_clause.size(), 2);
  TS_ASSERT_EQUALS(proof.getInstructions()[1].d_clause[0],
                   SatLiteral(128, false));
  TS_ASSERT_EQUALS(proof.getInstructions()[1].d_clause[1],
                   SatLiteral(8190, true));
}

void DratProofBlack::testOutputTwoAsText()
{
  // d -63 -8193
  // 129 -8191
  std::string input("\x64\x7f\x83\x80\x01\x00\x61\x82\x02\xff\x7f\x00", 12);
  DratProof proof = DratProof::fromBinary(input);

  std::ostringstream output;
  proof.outputAsText(output);

  std::istringstream tokens(output.str());
  std::string token;

  tokens >> token;
  TS_ASSERT_EQUALS(token, "d");

  tokens >> token;
  TS_ASSERT_EQUALS(token, "-63");

  tokens >> token;
  TS_ASSERT_EQUALS(token, "-8193");

  tokens >> token;
  TS_ASSERT_EQUALS(token, "0");

  tokens >> token;
  TS_ASSERT_EQUALS(token, "129");

  tokens >> token;
  TS_ASSERT_EQUALS(token, "-8191");

  tokens >> token;
  TS_ASSERT_EQUALS(token, "0");
}

void DratProofBlack::testOutputTwoAsLfsc()
{
  // d -63 -8193
  // 129 -8191
  std::string input("\x64\x7f\x83\x80\x01\x00\x61\x82\x02\xff\x7f\x00", 12);
  DratProof proof = DratProof::fromBinary(input);
  std::ostringstream lfsc;
  proof.outputAsLfsc(lfsc, 2);
  std::ostringstream lfscWithoutWhitespace;
  for (char c : lfsc.str())
  {
    if (!std::isspace(c))
    {
      lfscWithoutWhitespace << c;
    }
  }
  std::string expectedLfsc =
      "(DRATProofd (clc (neg bb.v62)  (clc (neg bb.v8192) cln))"
      "(DRATProofa (clc (pos bb.v128) (clc (neg bb.v8190) cln))"
      "DRATProofn))";
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
