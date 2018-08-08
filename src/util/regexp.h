/*********************                                                        */
/*! \file regexp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
#include "util/rational.h"

namespace CVC4 {

/** The CVC4 string class
 *
 * This data structure is the domain of values for the string type. It can also
 * be used as a generic utility for representing strings.
 */
class CVC4_PUBLIC String {
 public:
  /**
   * The start ASCII code. In our string representation below, we represent
   * characters using a vector d_vec of unsigned integers. We refer to this as
   * the "internal representation" for the string.
   *
   * We make unsigned integer 0 correspond to the 65th character ("A") in the
   * ASCII alphabet to make models intuitive. In particular, say if we have
   * a set of string variables that are distinct but otherwise unconstrained,
   * then the model may assign them "A", "B", "C", ...
   */
  static inline unsigned start_code() { return 65; }
  /**
   * This is the cardinality of the alphabet that is representable by this
   * class. Notice that this must be greater than or equal to the cardinality
   * of the alphabet that the string theory reasons about.
   */
  static inline unsigned num_codes() { return 256; }
  /**
   * Convert unsigned char to the unsigned used in the internal representation
   * in d_vec below.
   */
  static unsigned convertCharToUnsignedInt(unsigned char c);
  /** Convert the internal unsigned to a unsigned char. */
  static unsigned char convertUnsignedIntToChar(unsigned i);
  /** Does the internal unsigned correspond to a printable character? */
  static bool isPrintable(unsigned i);
  /** get the internal unsigned for ASCII code c. */
  static unsigned convertCodeToUnsignedInt(unsigned c);
  /** get the ASCII code number that internal unsigned i corresponds to. */
  static unsigned convertUnsignedIntToCode(unsigned i);

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
  /** is less than or equal to string y */
  bool isLeq(const String& y) const;
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

  /**
   * Returns true if this string corresponds in text to a number, for example
   * this returns true for strings "7", "12", "004", "0" and false for strings
   * "abc", "4a", "-4", "".
   */
  bool isNumber() const;
  /** Returns the corresponding rational for the text of this string. */
  Rational toNumber() const;

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

}  // namespace CVC4

#endif /* __CVC4__REGEXP_H */
