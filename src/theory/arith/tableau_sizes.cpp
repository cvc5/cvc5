#include "theory/arith/tableau_sizes.h"
#include "theory/arith/tableau.h"

namespace CVC4 {
namespace theory {
namespace arith {

uint32_t TableauSizes::getRowLength(ArithVar b) const {
  return d_tab->basicRowLength(b);
}

uint32_t TableauSizes::getColumnLength(ArithVar x) const {
  return d_tab->getColLength(x);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
