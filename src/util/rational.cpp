
#include "util/rational.h"

using namespace CVC4;

std::ostream& CVC4::operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
}
