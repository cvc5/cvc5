/*********************                                                        */
/*! \file regexp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__REGEXP_H
#define __CVC4__REGEXP_H

#include <cstddef>
#include <functional>
#include <ostream>
#include <string>
#include <vector>

namespace CVC4 {

class CVC4_PUBLIC String {
 public:
  static unsigned convertCharToUnsignedInt(unsigned char c) {
    unsigned i = c;
    i = i + 191;
    return (i >= 256 ? i - 256 : i);
  }
  static unsigned char convertUnsignedIntToChar(unsigned i) {
    unsigned ii = i + 65;
    return (unsigned char)(ii >= 256 ? ii - 256 : ii);
  }
  static bool isPrintable(unsigned i) {
    unsigned char c = convertUnsignedIntToChar(i);
    return (c >= ' ' && c <= '~');  // isprint( (int)c );
  }

  String() = default;
  explicit String(const std::string& s) : d_str(toInternal(s)) {}
  explicit String(const char* s) : d_str(toInternal(std::string(s))) {}
  explicit String(const unsigned char c)
      : d_str({convertCharToUnsignedInt(c)}) {}
  explicit String(const std::vector<unsigned>& s) : d_str(s) {}

  String& operator=(const String& y) {
    if (this != &y) {
      d_str = y.d_str;
    }
    return *this;
  }

  String concat(const String& other) const;

  bool operator==(const String& y) const { return cmp(y) == 0; }
  bool operator!=(const String& y) const { return cmp(y) != 0; }
  bool operator<(const String& y) const { return cmp(y) < 0; }
  bool operator>(const String& y) const { return cmp(y) > 0; }
  bool operator<=(const String& y) const { return cmp(y) <= 0; }
  bool operator>=(const String& y) const { return cmp(y) >= 0; }

  bool strncmp(const String& y, const std::size_t np) const;
  bool rstrncmp(const String& y, const std::size_t np) const;

  /*
   * Convenience functions
   */
  std::string toString() const;
  bool empty() const { return d_str.empty(); }
  bool isEmptyString() const { return empty(); }
  std::size_t size() const { return d_str.size(); }

  unsigned char getFirstChar() const { return getUnsignedCharAt(0); }
  unsigned char getLastChar() const { return getUnsignedCharAt(size() - 1); }

  bool isRepeated() const;
  bool tailcmp(const String& y, int& c) const;

  std::size_t find(const String& y, const std::size_t start = 0) const;
  std::size_t rfind(const String& y, const std::size_t start = 0) const;

  String replace(const String& s, const String& t) const;
  String substr(std::size_t i) const;
  String substr(std::size_t i, std::size_t j) const;

  String prefix(std::size_t i) const { return substr(0, i); }
  String suffix(std::size_t i) const { return substr(size() - i, i); }
  // if y=y1...yn and overlap returns m, then this is x1...y1...ym
  std::size_t overlap(const String& y) const;
  // if y=y1...yn and overlap returns m, then this is y(n+1-m)...yn...xk
  std::size_t roverlap(const String& y) const;

  bool isNumber() const;
  int toNumber() const;

  const std::vector<unsigned>& getVec() const { return d_str; }

 private:
  // guarded
  static unsigned char hexToDec(unsigned char c);

  static std::vector<unsigned> toInternal(const std::string& s);
  unsigned char getUnsignedCharAt(size_t pos) const;

  /**
   * Returns a negative number if *this < y, 0 if *this and y are equal and a
   * positive number if *this > y.
   */
  int cmp(const String& y) const;

  std::vector<unsigned> d_str;
}; /* class String */

namespace strings {

struct CVC4_PUBLIC StringHashFunction {
  size_t operator()(const ::CVC4::String& s) const {
    return std::hash<std::string>()(s.toString());
  }
}; /* struct StringHashFunction */

}  // namespace strings

std::ostream& operator<<(std::ostream& os, const String& s) CVC4_PUBLIC;

class CVC4_PUBLIC RegExp {
 public:
  RegExp() : d_type(1) {}
  explicit RegExp(const int t) : d_type(t) {}

  bool operator==(const RegExp& y) const { return d_type == y.d_type; }
  bool operator!=(const RegExp& y) const { return d_type != y.d_type; }
  bool operator<(const RegExp& y) const { return d_type < y.d_type; }
  bool operator>(const RegExp& y) const { return d_type > y.d_type; }
  bool operator<=(const RegExp& y) const { return d_type <= y.d_type; }
  bool operator>=(const RegExp& y) const { return d_type >= y.d_type; }

  int getType() const { return d_type; }

 private:
  int d_type;
}; /* class RegExp */

/**
 * Hash function for the RegExp constants.
 */
struct CVC4_PUBLIC RegExpHashFunction {
  inline size_t operator()(const RegExp& s) const {
    return (size_t)s.getType();
  }
}; /* struct RegExpHashFunction */

std::ostream& operator<<(std::ostream& os, const RegExp& s) CVC4_PUBLIC;

}  // namespace CVC4

#endif /* __CVC4__REGEXP_H */
