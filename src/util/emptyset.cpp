#include "util/emptyset.h"
#include <iostream>

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const EmptySet& asa) {
  return out << "emptyset(" << asa.getType() << ')';
}

}/* CVC4 namespace */
