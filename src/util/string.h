/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The string data type.
 */

#include "cvc5_public.h"

#ifndef CVC5__UTIL__STRING_H
#define CVC5__UTIL__STRING_H

#include <iosfwd>
#include <string>
#include <vector>

#include "util/rational.h"

namespace cvc5::internal {

namespace strings {
struct StringHashFunction;
}

/** The cvc5 string class
 *
 * This data structure is the domain of values for the string type. It can also
 * be used as a generic utility for representing strings.
 */
class String
{
  friend strings::StringHashFunction;

 public:
  /**
   * This is the cardinality of the alphabet that is representable by this
   * class. Notice that this must be greater than or equal to the cardinality
   * of the alphabet that the string theory reasons about.
   *
   * This must be strictly less than std::numeric_limits<unsigned>::max().
   *
   * As per the SMT-LIB standard for strings, we support the first 3 planes of
   * Unicode characters, where 196608 = 3*16^4.
   */
  static inline unsigned num_codes() { return 196608; }
  /** constructors for String
   *
   * Internally, a cvc5::internal::String is represented by a vector of unsigned
   * integers (d_str) representing the code points of the characters.
   *
   * To build a string from a C++ string, we may process escape sequences
   * according to the SMT-LIB standard. In particular, if useEscSequences is
   * true, we convert unicode escape sequences:
   *  \u d_3 d_2 d_1 d_0
   *  \u{d_0}
   *  \u{d_1 d_0}
   *  \u{d_2 d_1 d_0}
   *  \u{d_3 d_2 d_1 d_0}
   *  \u{d_4 d_3 d_2 d_1 d_0}
   * where d_0 ... d_4 are hexadecimal digits, to the appropriate character.
   *
   * If useEscSequences is false, then the characters of the constructed
   * cvc5::internal::String correspond one-to-one with the input string.
   */
  String() = default;
  explicit String(const std::string& s, bool useEscSequences = false)
      : d_str(toInternal(s, useEscSequences))
  {
  }
  explicit String(const std::wstring& s);
  explicit String(const char* s, bool useEscSequences = false)
      : d_str(toInternal(std::string(s), useEscSequences))
  {
  }
  explicit String(const std::vector<unsigned>& s);

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

  /**
   * Returns true if this string is equal to y for their first n characters.
   * If n is larger than the length of this string or y, this method returns
   * true if and only if this string is equal to y.
   */
  bool strncmp(const String& y, std::size_t n) const;
  /**
   * Returns true if this string is equal to y for their last n characters.
   * Similar to strncmp, if n is larger than the length of this string or y,
   * this method returns true if and only if this string is equal to y.
   */
  bool rstrncmp(const String& y, std::size_t n) const;

  /* toString
   * Converts this string to a std::string.
   *
   * The unprintable characters are converted to unicode escape sequences as
   * described above.
   *
   * If useEscSequences is false, the string's printable characters are
   * printed as characters. Notice that for all std::string s having only
   * printable characters, we have that
   *    cvc5::internal::String( s ).toString() = s.
   */
  std::string toString(bool useEscSequences = false) const;
  /* toWString
   * Converts this string to a std::wstring.
   *
   * Unlike toString(), this method uses no escape sequences as both this class
   * and std::wstring use 32bit characters.
   */
  std::wstring toWString() const;
  /** is this the empty string? */
  bool empty() const { return d_str.empty(); }
  /** is less than or equal to string y */
  bool isLeq(const String& y) const;
  /** Return the length of the string */
  std::size_t size() const { return d_str.size(); }

  bool isRepeated() const;
  bool tailcmp(const String& y, int& c) const;

  /**
   * Return the first position y occurs in this string, or std::string::npos
   * otherwise.
   */
  std::size_t find(const String& y, const std::size_t start = 0) const;
  /**
   * Return the first position y occurs in this string searching from the end,
   * or std::string::npos otherwise.
   */
  std::size_t rfind(const String& y, const std::size_t start = 0) const;
  /** Returns true if y is a prefix of this */
  bool hasPrefix(const String& y) const;
  /** Returns true if y is a suffix of this */
  bool hasSuffix(const String& y) const;
  /** Replace the character at index i in this string with t */
  String update(std::size_t i, const String& t) const;
  /** Replace the first occurrence of s in this string with t */
  String replace(const String& s, const String& t) const;
  /** Return the substring of this string starting at index i */
  String substr(std::size_t i) const;
  /** Return the substring of this string starting at index i with size at most
   * j */
  String substr(std::size_t i, std::size_t j) const;
  /** Return the prefix of this string of size at most i */
  String prefix(std::size_t i) const { return substr(0, i); }
  /** Return the suffix of this string of size at most i */
  String suffix(std::size_t i) const { return substr(size() - i, i); }

  /**
   * Checks if there is any overlap between this string and another string. This
   * corresponds to checking whether one string contains the other and whether a
   * substring of one is a prefix of the other and vice-versa.
   *
   * @param y The other string
   * @return True if there is an overlap, false otherwise
   */
  bool noOverlapWith(const String& y) const;

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
  /** Get the unsigned representation (code points) of this string */
  const std::vector<unsigned>& getVec() const { return d_str; }
  /**
   * Get the unsigned (code point) value of the first character in this string
   */
  unsigned front() const;
  /**
   * Get the unsigned (code point) value of the last character in this string
   */
  unsigned back() const;
  /** is the unsigned a digit?
   *
   * This is true for code points between 48 ('0') and 57 ('9').
   */
  static bool isDigit(unsigned character);
  /** is the unsigned a hexadecimal digit?
   *
   * This is true for code points between 48 ('0') and 57 ('9'), code points
   * between 65 ('A') and 70 ('F) and code points between 97 ('a') and 102 ('f).
   */
  static bool isHexDigit(unsigned character);
  /** is the unsigned a printable code point?
   *
   * This is true for Unicode 32 (' ') to 126 ('~').
   */
  static bool isPrintable(unsigned character);

  /**
   * Returns the maximum length of string representable by this class.
   * Corresponds to the maximum size of d_str.
   */
  static size_t maxSize();
 private:
  /**
   * Helper for toInternal: add character ch to vector vec, storing a string in
   * internal format. This throws an error if ch is not a printable character,
   * since non-printable characters must be escaped in SMT-LIB.
   */
  static void addCharToInternal(unsigned char ch, std::vector<unsigned>& vec);
  /**
   * Convert the string s to the internal format (vector of code points).
   * The argument useEscSequences is whether to process unicode escape
   * sequences.
   */
  static std::vector<unsigned> toInternal(const std::string& s,
                                          bool useEscSequences);

  /**
   * Returns a negative number if *this < y, 0 if *this and y are equal and a
   * positive number if *this > y.
   */
  int cmp(const String& y) const;

  std::vector<unsigned> d_str;
}; /* class String */

namespace strings {

struct StringHashFunction
{
  size_t operator()(const cvc5::internal::String& s) const;
}; /* struct StringHashFunction */

}  // namespace strings

std::ostream& operator<<(std::ostream& os, const String& s);

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__STRING_H */
