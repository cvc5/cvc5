/*********************                                                        */
/*! \file sha1_collision.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

/*
 * sha1smt.cpp
 *
 *  Created on: Jul 13, 2012
 *      Author: dejan
 */

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include <cvc4/cvc4.h>
#include <cvc4/expr/expr_iomanip.h>
#include <cvc4/options/set_language.h>
#include "sha1.hpp"
#include "word.h"

using namespace std;
using namespace CVC4;

hashsmt::cvc4_uchar8 *createInput(unsigned size, std::string prefix, std::ostream& output) {
  hashsmt::cvc4_uchar8 *input = new hashsmt::cvc4_uchar8[size];
  for(unsigned i = 0; i < size; ++i) {
    stringstream ss;
    ss << prefix << i;
    input[i] = hashsmt::cvc4_uchar8(ss.str());
    output << DeclareFunctionCommand(ss.str(), input[i].getExpr(), input[i].getExpr().getType()) << endl;
  }
  return input;
}

int main(int argc, char* argv[]) {

  try {

    // Check the arguments
    if (argc != 4) {
      cerr << "usage: sha1smt size rounds (1..80) output-file" << std::endl;
      return 1;
    }

    // Get the input size to encode
    unsigned msgSize;
    istringstream msgSize_is(argv[1]);
    msgSize_is >> msgSize;

    // Get the number of rounds to use
    unsigned rounds;
    istringstream rounds_is(argv[2]);
    rounds_is >> rounds;

    // The output
    ofstream output(argv[3]);
    output << expr::ExprSetDepth(-1) << language::SetLanguage(language::output::LANG_SMTLIB_V2);
    output << SetBenchmarkLogicCommand("QF_BV") << endl;
    output << SetBenchmarkStatusCommand(SMT_UNSATISFIABLE) << endl;

    // Make the variables the size of the string
    hashsmt::cvc4_uchar8 *cvc4input1 = createInput(msgSize, "x", output);
    hashsmt::cvc4_uchar8 *cvc4input2 = createInput(msgSize, "y", output);

    // Do the cvc4 encoding for first message
    hashsmt::sha1 cvc4encoder1(rounds);
    cvc4encoder1.process_bytes(cvc4input1, msgSize);
    hashsmt::cvc4_uint32 cvc4digest1[5];
    cvc4encoder1.get_digest(cvc4digest1);

    // Do the cvc4 encoding for second message
    hashsmt::sha1 cvc4encoder2(rounds);
    cvc4encoder2.process_bytes(cvc4input2, msgSize);
    hashsmt::cvc4_uint32 cvc4digest2[5];
    cvc4encoder2.get_digest(cvc4digest2);

    // Create the assertion
    Expr inputEqual = (hashsmt::Word::concat(cvc4input1, msgSize) == hashsmt::Word::concat(cvc4input2, msgSize));
    Expr digestEqual = (hashsmt::Word::concat(cvc4digest1, 5) == hashsmt::Word::concat(cvc4digest2, 5));
    Expr assertion = inputEqual.notExpr().andExpr(digestEqual);

    output << AssertCommand(assertion) << endl;

    // Checksat command
    output << CheckSatCommand() << endl;

    delete[] cvc4input1;
    delete[] cvc4input2;

  } catch (CVC4::Exception& e) {
    cerr << e << endl;
  }
}
