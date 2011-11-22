%{
#include "util/stats.h"
%}

namespace CVC4 {
  template <class T> class CVC4_PUBLIC BackedStat;

  %template(int64_t_BackedStat) BackedStat<int64_t>;
  %template(double_BackedStat) BackedStat<double>;
  %template(timespec_BackedStat) BackedStat<timespec>;
}/* CVC4 namespace */

%ignore CVC4::operator<<(std::ostream&, const timespec&);

%rename(increment) CVC4::IntStat::operator++();
%rename(plusAssign) CVC4::IntStat::operator+=(int64_t);

%rename(plusAssign) CVC4::operator+=(timespec&, const timespec&);
%rename(minusAssign) CVC4::operator-=(timespec&, const timespec&);
%rename(plus) CVC4::operator+(const timespec&, const timespec&);
%rename(minus) CVC4::operator-(const timespec&, const timespec&);
%rename(equals) CVC4::operator==(const timespec&, const timespec&);
%ignore CVC4::operator!=(const timespec&, const timespec&);
%rename(less) CVC4::operator<(const timespec&, const timespec&);
%rename(lessEqual) CVC4::operator<=(const timespec&, const timespec&);
%rename(greater) CVC4::operator>(const timespec&, const timespec&);
%rename(greaterEqual) CVC4::operator>=(const timespec&, const timespec&);

%include "util/stats.h"

