/*********************                                                        */
/*! \file sha1_inversion.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

#include <boost/uuid/sha1.hpp>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "expr/expr_iomanip.h"
#include "options/language.h"
#include "options/set_language.h"
#include "sha1.hpp"
#include "smt/command.h"
#include "word.h"

using namespace std;
using namespace CVC4;

int main(int argc, char* argv[]) {

  try {

    // Check the arguments
    if (argc != 3) {
      cerr << "usage: sha1smt message output-file" << std::endl;
      return 1;
    }

    // Get the message to encode and the output file
    string msg = argv[1];
    unsigned msgSize = msg.size();
    ofstream output(argv[2]);
    output << expr::ExprSetDepth(-1) << language::SetLanguage(language::output::LANG_SMTLIB_V2);
    output << SetBenchmarkLogicCommand("QF_BV") << endl;
    output << SetBenchmarkStatusCommand(SMT_SATISFIABLE) << endl;

    // Make the variables the size of the string
    hashsmt::cvc4_uchar8 *cvc4input = new hashsmt::cvc4_uchar8[msgSize];
    for (unsigned i = 0; i < msgSize; ++ i) {
      stringstream ss;
      ss << "x" << i;
      cvc4input[i] = hashsmt::cvc4_uchar8(ss.str());
      output << DeclareFunctionCommand(ss.str(), cvc4input[i].getExpr(), cvc4input[i].getExpr().getType()) << endl;

      // Ouput the solution also
      Expr solution = (cvc4input[i] == hashsmt::cvc4_uchar8(msg.c_str()[i]));
      output << "; " << AssertCommand(solution) << endl;
    }

    // Do the cvc4 encoding
    hashsmt::sha1 cvc4encoder;
    cvc4encoder.process_bytes(cvc4input, msgSize);

    // Get the digest as bitvectors
    hashsmt::cvc4_uint32 cvc4digest[5];
    cvc4encoder.get_digest(cvc4digest);

    // Do the actual sha1 encoding
    boost::uuids::detail::sha1 sha1encoder;
    sha1encoder.process_bytes(msg.c_str(), msgSize);
    unsigned sha1digest[5];
    sha1encoder.get_digest(sha1digest);

    // Create the assertion
    Expr assertion;
    for (unsigned i = 0; i < 5; ++ i) {
      Expr conjunct = (cvc4digest[i] == hashsmt::cvc4_uint32(sha1digest[i]));
      if (i > 0) {
        assertion = assertion.andExpr(conjunct);
      } else {
        assertion = conjunct;
      }
    }
    output << AssertCommand(assertion) << endl;

    // Checksat command
    output << CheckSatCommand() << endl;

    delete cvc4input;

  } catch (CVC4::Exception& e) {
    cerr << e << endl;
  }
}
