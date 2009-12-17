/* Black box testing of CVC4::Node. */

#include <cxxtest/TestSuite.h>
//#include <string>
#include <sstream>

#include "expr/expr_manager.h"
#include "parser/cvc/cvc_parser.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace std;

const string d_goodInputs[] = {
      "ASSERT TRUE;",
      "QUERY TRUE;",
      "CHECKSAT FALSE;",
      "a, b : BOOLEAN;",
      "x, y : INT;",
      "a, b : BOOLEAN; QUERY (a => b) AND a => b;"
  };

class CvcParserBlack : public CxxTest::TestSuite {
private:

  ExprManager *d_exprManager;


public:
  void setUp() {
//    cout << "In setUp()\n";
    d_exprManager = new ExprManager();
//    cout << "Leaving setUp()\n";
  }

  void testGoodInputs() {
//    cout << "In testGoodInputs()\n";
    for( int i=0; i < sizeof(d_goodInputs); ++i ) {
      istringstream stream(d_goodInputs[i]);
      CvcParser cvcParser(d_exprManager,stream);
      TS_ASSERT( !cvcParser.done() );
      while( !cvcParser.done() ) {
        TS_ASSERT( cvcParser.parseNextCommand() );
      }
  }
};
