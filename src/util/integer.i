%{
#include "util/integer.h"
%}

%ignore CVC4::Integer::Integer(int);
%ignore CVC4::Integer::Integer(unsigned int);
%ignore CVC4::Integer::Integer(const std::string&);
%ignore CVC4::Integer::Integer(const std::string&, unsigned int);

%rename(assign) CVC4::Integer::operator=(const Integer&);
%rename(equals) CVC4::Integer::operator==(const Integer&) const;
%ignore CVC4::Integer::operator!=(const Integer&) const;
%rename(plus) CVC4::Integer::operator+(const Integer&) const;
%rename(minus) CVC4::Integer::operator-() const;
%rename(minus) CVC4::Integer::operator-(const Integer&) const;
%rename(times) CVC4::Integer::operator*(const Integer&) const;
%rename(dividedBy) CVC4::Integer::operator/(const Integer&) const;
%rename(modulo) CVC4::Integer::operator%(const Integer&) const;
%rename(plusAssign) CVC4::Integer::operator+=(const Integer&);
%rename(minusAssign) CVC4::Integer::operator-=(const Integer&);
%rename(timesAssign) CVC4::Integer::operator*=(const Integer&);
%rename(dividedByAssign) CVC4::Integer::operator/=(const Integer&);
%rename(moduloAssign) CVC4::Integer::operator%=(const Integer&);
%rename(less) CVC4::Integer::operator<(const Integer&) const;
%rename(lessEqual) CVC4::Integer::operator<=(const Integer&) const;
%rename(greater) CVC4::Integer::operator>(const Integer&) const;
%rename(greaterEqual) CVC4::Integer::operator>=(const Integer&) const;

%rename(apply) CVC4::IntegerHashFunction::operator()(const CVC4::Integer&) const;

%ignore CVC4::operator<<(std::ostream&, const Integer&);

%include "util/integer.h"
