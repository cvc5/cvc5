%{
#include "util/rational.h"
%}

%ignore CVC4::RationalFromDoubleException::RationalFromDoubleException(double);

%ignore CVC4::Rational::Rational(int);
%ignore CVC4::Rational::Rational(unsigned int);
%ignore CVC4::Rational::Rational(int, int);
%ignore CVC4::Rational::Rational(unsigned int, unsigned int);
%ignore CVC4::Rational::Rational(const std::string&);
%ignore CVC4::Rational::Rational(const std::string&, unsigned int);

%rename(assign) CVC4::Rational::operator=(const Rational&);
%rename(equals) CVC4::Rational::operator==(const Rational&) const;
%ignore CVC4::Rational::operator!=(const Rational&) const;
%rename(plus) CVC4::Rational::operator+(const Rational&) const;
%rename(minus) CVC4::Rational::operator-() const;
%rename(minus) CVC4::Rational::operator-(const Rational&) const;
%rename(times) CVC4::Rational::operator*(const Rational&) const;
%rename(dividedBy) CVC4::Rational::operator/(const Rational&) const;
%rename(plusAssign) CVC4::Rational::operator+=(const Rational&);
%rename(minusAssign) CVC4::Rational::operator-=(const Rational&);
%rename(timesAssign) CVC4::Rational::operator*=(const Rational&);
%rename(dividedByAssign) CVC4::Rational::operator/=(const Rational&);
%rename(less) CVC4::Rational::operator<(const Rational&) const;
%rename(lessEqual) CVC4::Rational::operator<=(const Rational&) const;
%rename(greater) CVC4::Rational::operator>(const Rational&) const;
%rename(greaterEqual) CVC4::Rational::operator>=(const Rational&) const;

%rename(apply) CVC4::RationalHashFunction::operator()(const CVC4::Rational&) const;

%ignore CVC4::operator<<(std::ostream&, const Rational&);

%include "util/rational.h"
