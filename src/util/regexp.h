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

  /** constructors for String
  *
  * Internally, a CVC4::String is represented by a vector of unsigned
  * integers (d_str), where the correspondence between C++ characters
  * to and from unsigned integers is determined by
  * by convertCharToUnsignedInt and convertUnsignedIntToChar.
  *
  * If useEscSequences is true, then the escape sequences in the input
  * are converted to the corresponding character. This constructor may
  * throw an exception if the input contains unrecognized escape sequences.
  * Currently supported escape sequences are \n, \t, \v, \b, \r, \f, \a, \\,
  * \x[N] where N is a hexidecimal, and octal escape sequences of the
  * form \[c1]([c2]([c3])?)? where c1, c2, c3 are digits from 0 to 7.
  *
  * If useEscSequences is false, then the characters of the constructed
  * CVC4::String correspond one-to-one with the input string.
  */
  String() = default;
  explicit String(const std::string& s, bool useEscSequences = false)
      : d_str(toInternal(s, useEscSequences)) {}
  explicit String(const char* s, bool useEscSequences = false)
      : d_str(toInternal(std::string(s), useEscSequences)) {}
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

  /* toString
  * Converts this string to a std::string.
  *
  * If useEscSequences is true, then unprintable characters
  * are converted to escape sequences. The escape sequences
  * \n, \t, \v, \b, \r, \f, \a, \\ are printed in this way.
  * For all other unprintable characters, we print \x[N] where
  * [N] is the 2 digit hexidecimal corresponding to value of
  * the character.
  *
  * If useEscSequences is false, the returned std::string's characters
  * map one-to-one with the characters in this string.
  * Notice that for all std::string s, we have that
  *    CVC4::String( s ).toString() = s.
  */
  std::string toString(bool useEscSequences = false) const;
  /** is this the empty string? */
  bool empty() const { return d_str.empty(); }
  /** is this the empty string? */
  bool isEmptyString() const { return empty(); }
  /** Return the length of the string */
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
  /** string overlap
  *
  * if overlap returns m>0,
  * then the maximal suffix of this string that is a prefix of y is of length m.
  *
  * For example, if x is "abcdef", then:
  * x.overlap("defg") = 3
  * x.overlap("ab") = 0
  * x.overlap("d") = 0
  * x.overlap("bcdefdef") = 5
  */
  std::size_t overlap(const String& y) const;
  /** string reverse overlap
  *
  * if roverlap returns m>0,
  * then the maximal prefix of this string that is a suffix of y is of length m.
  *
  * For example, if x is "abcdef", then:
  * x.roverlap("aaabc") = 3
  * x.roverlap("def") = 0
  * x.roverlap("d") = 0
  * x.roverlap("defabcde") = 5
  *
  * Notice that x.overlap(y) = y.roverlap(x)
  */
  std::size_t roverlap(const String& y) const;

  bool isNumber() const;
  int toNumber() const;

  const std::vector<unsigned>& getVec() const { return d_str; }
  /** is the unsigned a digit?
  * The input should be the same type as the element type of d_str
  */
  static bool isDigit(unsigned character);

  /**
   * Returns the maximum length of string representable by this class.
   * Corresponds to the maximum size of d_str.
   */
  static size_t maxSize();
 private:
  // guarded
  static unsigned char hexToDec(unsigned char c);

  static std::vector<unsigned> toInternal(const std::string& s,
                                          bool useEscSequences = true);
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
