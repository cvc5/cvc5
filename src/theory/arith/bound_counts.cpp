#include "theory/arith/bound_counts.h"
#include "theory/arith/tableau.h"

namespace CVC4 {
namespace theory {
namespace arith {

const BoundsInfo& BoundCountingLookup::boundsInfo(ArithVar basic) const {
  RowIndex ridx = d_tab->basicToRowIndex(basic);
  Assert(d_bc->isKey(ridx));
  return (*d_bc)[ridx];
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
