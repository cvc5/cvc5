%{
#include "util/cardinality.h"
%}

%feature("valuewrapper") CVC4::CardinalityBeth;

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
%ignore CVC4::operator<<(std::ostream&, CardinalityBeth);

%include "util/cardinality.h"
