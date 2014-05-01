#include "cvc4autoconfig.h"
#include "util/integer.h"
#include <string>
#include <sstream>

#ifndef CVC4_CLN_IMP
#  error "This source should only ever be built if CVC4_CLN_IMP is on !"
#endif /* CVC4_CLN_IMP */

using namespace std;
using namespace CVC4;


void Integer::parseInt(const std::string& s, unsigned base) throw(std::invalid_argument) {
  cln::cl_read_flags flags;
  flags.syntax = cln::syntax_integer;
  flags.lsyntax = cln::lsyntax_standard;
  flags.rational_base = base;
  if(base == 0) {
    // infer base in a manner consistent with GMP
    if(s[0] == '0') {
      flags.lsyntax = cln::lsyntax_commonlisp;
      std::string st = s;
      if(s[1] == 'X' || s[1] == 'x') {
        st.replace(0, 2, "#x");
      } else if(s[1] == 'B' || s[1] == 'b') {
        st.replace(0, 2, "#b");
      } else {
        st.replace(0, 1, "#o");
      }
      readInt(flags, st, base);
      return;
    } else {
      flags.rational_base = 10;
    }
  }
  readInt(flags, s, base);
}

void Integer::readInt(const cln::cl_read_flags& flags, const std::string& s, unsigned base) throw(std::invalid_argument) {
  try {
    // Removing leading zeroes, CLN has a bug for these inputs up to and
    // including CLN v1.3.2.
    // See http://www.ginac.de/CLN/cln.git/?a=commit;h=4a477b0cc3dd7fbfb23b25090ff8c8869c8fa21a for details.
    size_t pos = s.find_first_not_of('0');
    if(pos == std::string::npos) {
      d_value = read_integer(flags, "0", NULL, NULL);
    } else {
      const char* cstr = s.c_str();
      const char* start = cstr + pos;
      const char* end = cstr + s.length();
      d_value = read_integer(flags, start, end, NULL);
    }
  } catch(...) {
    std::stringstream ss;
    ss << "Integer() failed to parse value \"" << s << "\" in base " << base;
    throw std::invalid_argument(ss.str());
  }
}

bool Integer::fitsSignedInt() const {
  // TODO improve performance
  return d_value <= std::numeric_limits<signed int>::max() &&
    d_value >= std::numeric_limits<signed int>::min();
}

bool Integer::fitsUnsignedInt() const {
  // TODO improve performance
  return sgn() >= 0 && d_value <= std::numeric_limits<unsigned int>::max();
}

signed int Integer::getSignedInt() const {
  // ensure there isn't overflow
  CheckArgument(fitsSignedInt(), this, "Overflow detected in Integer::getSignedInt()");
  return cln::cl_I_to_int(d_value);
}

unsigned int Integer::getUnsignedInt() const {
  // ensure there isn't overflow
  CheckArgument(fitsUnsignedInt(), this, "Overflow detected in Integer::getUnsignedInt()");
  return cln::cl_I_to_uint(d_value);
}
