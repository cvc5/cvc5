#include "util/integer.h"

using namespace CVC4;

std::ostream& CVC4::operator<<(std::ostream& os, const Integer& n){
  return os << n.toString();
}
