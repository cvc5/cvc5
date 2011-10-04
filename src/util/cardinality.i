%{
#include "util/cardinality.h"
%}

%feature("valuewrapper") CVC4::Cardinality::Beth;

%rename(plusAssign) CVC4::Cardinality::operator+=(const Cardinality&);
%rename(timesAssign) CVC4::Cardinality::operator*=(const Cardinality&);
%rename(powerAssign) CVC4::Cardinality::operator^=(const Cardinality&);
%rename(plus) CVC4::Cardinality::operator+(const Cardinality&) const;
%rename(times) CVC4::Cardinality::operator*(const Cardinality&) const;
%rename(power) CVC4::Cardinality::operator^(const Cardinality&) const;
%rename(equals) CVC4::Cardinality::operator==(const Cardinality&) const;
%ignore CVC4::Cardinality::operator!=(const Cardinality&) const;
%rename(less) CVC4::Cardinality::operator<(const Cardinality&) const;
%rename(lessEqual) CVC4::Cardinality::operator<=(const Cardinality&) const;
%rename(greater) CVC4::Cardinality::operator>(const Cardinality&) const;
%rename(greaterEqual) CVC4::Cardinality::operator>=(const Cardinality&) const;

%ignore CVC4::operator<<(std::ostream&, const Cardinality&);
%ignore CVC4::operator<<(std::ostream&, Cardinality::Beth);

  class Beth {
    Integer d_index;

  public:
    Beth(const Integer& beth) : d_index(beth) {
      CheckArgument(beth >= 0, beth,
                    "Beth index must be a nonnegative integer, not %s.",
                    beth.toString().c_str());
    }

    const Integer& getNumber() const throw() {
      return d_index;
    }
  };/* class Cardinality::Beth */

  class Unknown {
  public:
    Unknown() throw() {}
    ~Unknown() throw() {}
  };/* class Cardinality::Unknown */

%include "util/cardinality.h"

%{
namespace CVC4 {
  typedef CVC4::Cardinality::Beth Beth;
  typedef CVC4::Cardinality::Unknown Unknown;
}
%}
