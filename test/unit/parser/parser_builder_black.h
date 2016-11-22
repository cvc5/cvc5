/*********************                                                        */
/*! \file parser_builder_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::parser::ParserBuilder.
 **
 ** Black box testing of CVC4::parser::ParserBuilder.
 **/

#include <cxxtest/TestSuite.h>

#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include <fstream>
#include <iostream>

#include "options/language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::language::input;
using namespace std;

class ParserBuilderBlack : public CxxTest::TestSuite {

  ExprManager *d_exprManager;

  void checkEmptyInput(ParserBuilder& builder) {
    Parser *parser = builder.build();
    TS_ASSERT( parser != NULL );

    Expr e = parser->nextExpression();
    TS_ASSERT( e.isNull() );

    delete parser;
  }

  void checkTrueInput(ParserBuilder& builder) {
    Parser *parser = builder.build();
    TS_ASSERT( parser != NULL );

    Expr e = parser->nextExpression();
    TS_ASSERT_EQUALS( e, d_exprManager->mkConst(true) );

    e = parser->nextExpression();
    TS_ASSERT( e.isNull() );
    delete parser;
  }

  char* mkTemp() {
    char *filename = strdup("/tmp/testinput.XXXXXX");
    int fd = mkstemp(filename);
    TS_ASSERT( fd != -1 );
    close(fd);
    return filename;
  }

public:

  void setUp() {
    d_exprManager = new ExprManager;
  }

  void tearDown() {
    delete d_exprManager;
  }

  void testEmptyFileInput() {
    char *filename = mkTemp();

    checkEmptyInput(
      ParserBuilder(d_exprManager,filename)
        .withInputLanguage(LANG_CVC4)
                    );

    remove(filename);
    free(filename);
  }

  void testSimpleFileInput() {
    char *filename = mkTemp();

    std::fstream fs( filename, fstream::out );
    fs << "TRUE" << std::endl;
    fs.close();

    checkTrueInput(
      ParserBuilder(d_exprManager,filename)
        .withInputLanguage(LANG_CVC4)
                   );

    remove(filename);
    free(filename);
  }

  void testEmptyStringInput() {
    checkEmptyInput(
      ParserBuilder(d_exprManager,"foo")
        .withInputLanguage(LANG_CVC4)
        .withStringInput("")
                    );
  }

  void testTrueStringInput() {
    checkTrueInput(
      ParserBuilder(d_exprManager,"foo")
        .withInputLanguage(LANG_CVC4)
        .withStringInput("TRUE")
                   );
  }

  void testEmptyStreamInput() {
    stringstream ss( "", ios_base::in );
    checkEmptyInput(
      ParserBuilder(d_exprManager,"foo")
        .withInputLanguage(LANG_CVC4)
        .withStreamInput(ss)
                    );
  }

  void testTrueStreamInput() {
    stringstream ss( "TRUE", ios_base::in );
    checkTrueInput(
      ParserBuilder(d_exprManager,"foo")
        .withInputLanguage(LANG_CVC4)
        .withStreamInput(ss)
                   );
  }



}; // class ParserBuilderBlack
