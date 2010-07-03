#include <set>
#include "expr/kind.h"
#include "expr/node.h"
#include "util/Assert.h"


namespace CVC4 {
namespace theory {
namespace arith {

struct RightHandRationalLT
{
  bool operator()(TNode s1, TNode s2) const
  {
    TNode rh1 = s1[1];
    TNode rh2 = s2[1];
    const Rational& c1 = rh1.getConst<Rational>();
    const Rational& c2 = rh2.getConst<Rational>();
    int cmpRes = c1.cmp(c2);
    return cmpRes < 0;
  }
};

typedef std::set<Node, RightHandRationalLT> OrderedSet;

struct SetCleanupStrategy{
  static void cleanup(OrderedSet* l){
    Debug("arithgc") << "cleaning up  " << l << "\n";
    delete l;
  }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
