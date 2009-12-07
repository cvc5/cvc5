/* White box testing of CVC4::Expr. */

#include <cxxtest/TestSuite.h>

#include "expr/expr.h"

using namespace CVC4;

class ExprWhite : public CxxTest::TestSuite {
public:

  void testNull() {
    Expr::s_null;
  }

  void testCopyCtor() {
    Expr e(Expr::s_null);
  }
};
