/* Black box testing of CVC4::Node. */

#include <cxxtest/TestSuite.h>

#include "expr/node.h"

using namespace CVC4;

class NodeBlack : public CxxTest::TestSuite {
public:

  void testNull() {
    Node::s_null;
  }

  void testCopyCtor() {
    Node e(Node::s_null);
  }
};
