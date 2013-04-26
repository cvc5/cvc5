
#include "cvc4_private.h"

#pragma once

#include <stdint.h>
#include "theory/arith/arithvar.h"

namespace CVC4 {
namespace theory {
namespace arith {

class Tableau;

class TableauSizes {
private:
  const Tableau* d_tab;
public:
  TableauSizes(const Tableau* tab): d_tab(tab){}

  uint32_t getRowLength(ArithVar b) const;
  uint32_t getColumnLength(ArithVar x) const;
}; /* TableauSizes */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

