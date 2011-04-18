#include <map>
#include <set>
#include "expr/kind.h"
#include "expr/node.h"
#include "util/Assert.h"
#include "theory/arith/arith_utilities.h"


namespace CVC4 {
namespace theory {
namespace arith {

inline const Rational& rightHandRational(TNode ineq){
  Assert(ineq.getKind() == kind::LEQ
         || ineq.getKind() == kind::GEQ
         || ineq.getKind() == kind::EQUAL);
  TNode righthand = ineq[1];
  Assert(righthand.getKind() == kind::CONST_RATIONAL);
  return righthand.getConst<Rational>();
}

class BoundValueEntry {
private:
  const Rational& value;
  TNode d_leq, d_geq;

  BoundValueEntry(const Rational& v, TNode l, TNode g):
    value(v),
    d_leq(l),
    d_geq(g)
  {}

public:
  Node getLeq() const{
    Assert(hasLeq());
    return d_leq;
  }
  Node getGeq() const{
    Assert(hasGeq());
    return d_geq;
  }

  static BoundValueEntry mkFromLeq(TNode leq){
    Assert(leq.getKind() == kind::LEQ);
    return BoundValueEntry(rightHandRational(leq), leq, TNode::null());
  }

  static BoundValueEntry mkFromGeq(TNode geq){
    Assert(geq.getKind() == kind::GEQ);
    return BoundValueEntry(rightHandRational(geq), TNode::null(), geq);
  }

  void addLeq(TNode leq){
    Assert(leq.getKind() == kind::LEQ);
    Assert(rightHandRational(leq) == getValue());
    Assert(!hasLeq());
    d_leq = leq;
  }

  void addGeq(TNode geq){
    Assert(geq.getKind() == kind::GEQ);
    Assert(rightHandRational(geq) == getValue());
    Assert(!hasGeq());
    d_geq = geq;
  }

  bool hasGeq() const { return d_geq != TNode::null(); }
  bool hasLeq() const { return d_leq != TNode::null(); }


  const Rational& getValue() const{
    return value;
  }

  bool operator<(const BoundValueEntry& other){
    return value < other.value;
  }
};

typedef std::map<Rational, BoundValueEntry> BoundValueSet;

typedef std::set<TNode, RightHandRationalLT> EqualValueSet;

// struct SetCleanupStrategy{
//   static void cleanup(OrderedSet* l){
//     Debug("arithgc") << "cleaning up  " << l << "\n";
//     delete l;
//   }
// };

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
