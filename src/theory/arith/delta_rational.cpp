
#include "theory/arith/delta_rational.h"

using namespace std;
using namespace CVC4;

std::ostream& CVC4::operator<<(std::ostream& os, const DeltaRational& dq){
  return os << "(" << dq.getNoninfintestimalPart()
            << "," << dq.getInfintestimalPart() << ")";
}


std::string DeltaRational::toString() const {
  return "(" + getNoninfintestimalPart().toString() + "," +
    getInfintestimalPart().toString() + ")";
}
