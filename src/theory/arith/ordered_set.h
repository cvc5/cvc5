#include <set>
#include "expr/kind.h"
#include "expr/node.h"
#include "util/Assert.h"
#include "theory/arith/arith_utilities.h"


namespace CVC4 {
namespace theory {
namespace arith {


typedef std::set<TNode, RightHandRationalLT> OrderedSet;

struct SetCleanupStrategy{
  static void cleanup(OrderedSet* l){
    Debug("arithgc") << "cleaning up  " << l << "\n";
    delete l;
  }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
