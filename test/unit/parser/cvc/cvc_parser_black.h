/* Black box testing of CVC4::parser::CvcParser. */

#include <cxxtest/TestSuite.h>
//#include <string>
#include <sstream>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "parser/cvc/cvc_parser.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace std;

const string goodInputs[] = {
      "", // empty string is OK
      "ASSERT TRUE;",
      "QUERY TRUE;",
      "CHECKSAT FALSE;",
      "a, b : BOOLEAN;",
      "x, y : INT;",
      "a, b : BOOLEAN; QUERY (a => b) AND a => b;",
      "%% nothing but a comment",
      "% a comment\nASSERT TRUE %a command\n% another comment"
  };

/* The following expressions are good in a context where a, b, and c have been declared as BOOLEAN. */
const string goodBooleanExprs[] = {
    "a AND b",
    "a AND b OR c",
    "(a => b) AND a => b",
    "(a <=> b) AND (NOT a)",
    "(a XOR b) <=> (a OR b) AND (NOT (a AND b))"
};

const string badInputs[] = {
      ";", // no command
      "ASSERT;", // no args
      "QUERY",
      "CHECKSAT;",
      "a, b : boolean;", // lowercase boolean isn't a type
      "0x : INT;", // 0x isn't an identifier
      "a, b : BOOLEAN\nQUERY (a => b) AND a => b;" // no semicolon after decl
  };

/* The following expressions are bad even in a context where a, b, and c have been declared as BOOLEAN. */
const string badBooleanExprs[] = {
    "",
    "a AND", // wrong arity
    "AND(a,b)", // not infix
    "(OR (AND a b) c)", // not infix
    "a IMPLIES b", // should be =>
    "a NOT b", // wrong arity, not infix
    "a and b" // wrong case
};

class CvcParserBlack : public CxxTest::TestSuite {
private:
  ExprManager *d_exprManager;

public:
  void setUp() {
    d_exprManager = new ExprManager();
  }

  void testGoodInputs() {
    //    cout << "In testGoodInputs()\n";
    for(int i = 0; i < sizeof(goodInputs); ++i) {
      istringstream stream(goodInputs[i]);
      CvcParser cvcParser(d_exprManager, stream);
      TS_ASSERT( !cvcParser.done() );
      while(!cvcParser.done()) {
        TS_ASSERT( cvcParser.parseNextCommand() != NULL );
      }
    }
  }

  void testBadInputs() {
    //    cout << "In testGoodInputs()\n";
    for(int i = 0; i < sizeof(badInputs); ++i) {
      istringstream stream(badInputs[i]);
      CvcParser cvcParser(d_exprManager, stream);
      TS_ASSERT_THROWS( cvcParser.parseNextCommand(), ParserException );
    }
  }

  void testGoodBooleanExprs() {
    //    cout << "In testGoodInputs()\n";
    for(int i = 0; i < sizeof(goodBooleanExprs); ++i) {
      istringstream stream(goodBooleanExprs[i]);
      CvcParser cvcParser(d_exprManager, stream);
      TS_ASSERT( !cvcParser.done() );
      while(!cvcParser.done()) {
        TS_ASSERT( !cvcParser.parseNextExpression().isNull() );
      }
    }
  }

  void testBadBooleanExprs() {
    //    cout << "In testGoodInputs()\n";
    for(int i = 0; i < sizeof(badBooleanExprs); ++i) {
      istringstream stream(badBooleanExprs[i]);
      CvcParser cvcParser(d_exprManager, stream);
      TS_ASSERT_THROWS( cvcParser.parseNextExpression(), ParserException );
    }
  }

};
