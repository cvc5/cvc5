
#include "options/theoryof_mode.h"

#include <ostream>
#include "base/cvc4_assert.h"

namespace CVC4 {
namespace theory {

std::ostream& operator<<(std::ostream& out, TheoryOfMode m) throw() {
  switch(m) {
  case THEORY_OF_TYPE_BASED: return out << "THEORY_OF_TYPE_BASED";
  case THEORY_OF_TERM_BASED: return out << "THEORY_OF_TERM_BASED";
  default: return out << "TheoryOfMode!UNKNOWN";
  }

  Unreachable();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
