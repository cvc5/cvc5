/*********************                                                        */
/*! \file sequence.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The sequence data type.
 **/

#ifndef CVC4__EXPR__SEQUENCE_H
#define CVC4__EXPR__SEQUENCE_H

#include <vector>
#include "expr/node.h"

namespace CVC4 {

/** The CVC4 sequence class
 *
 * This data structure is the domain of values for the sequence type.
 */
class Sequence
{
 public:
  /** constructors for Sequence
   *
   * Internally, a CVC4::Sequence is represented by a vector of Nodes (d_seq),
   * where each Node in this vector must be a constant.
   */
  Sequence() = default;
  explicit Sequence(TypeNode t, const std::vector<Node>& s);

  Sequence& operator=(const Sequence& y)
  {
    if (this != &y)
    {
      d_seq = y.d_seq;
    }
    return *this;
  }

  Sequence concat(const Sequence& other) const;

  bool operator==(const Sequence& y) const { return cmp(y) == 0; }
  bool operator!=(const Sequence& y) const { return cmp(y) != 0; }
  bool operator<(const Sequence& y) const { return cmp(y) < 0; }
  bool operator>(const Sequence& y) const { return cmp(y) > 0; }
  bool operator<=(const Sequence& y) const { return cmp(y) <= 0; }
  bool operator>=(const Sequence& y) const { return cmp(y) >= 0; }

  bool strncmp(const Sequence& y, std::size_t n) const;
  bool rstrncmp(const Sequence& y, std::size_t n) const;

  /** is this the empty string? */
  bool empty() const { return d_seq.empty(); }
  /** is less than or equal to string y */
  bool isLeq(const Sequence& y) const;
  /** Return the length of the string */
  std::size_t size() const { return d_seq.size(); }

  bool isRepeated() const;
  bool tailcmp(const Sequence& y, int& c) const;

  /**
   * Return the first position y occurs in this string, or std::string::npos
   * otherwise.
   */
  std::size_t find(const Sequence& y, const std::size_t start = 0) const;
  /**
   * Return the first position y occurs in this string searching from the end,
   * or std::string::npos otherwise.
   */
  std::size_t rfind(const Sequence& y, const std::size_t start = 0) const;
  /** Returns true if y is a prefix of this */
  bool hasPrefix(const Sequence& y) const;
  /** Returns true if y is a suffix of this */
  bool hasSuffix(const Sequence& y) const;
  /** Replace the first occurrence of s in this string with t */
  Sequence replace(const Sequence& s, const Sequence& t) const;
  /** Return the substring of this string starting at index i */
  Sequence substr(std::size_t i) const;
  /** Return the substring of this string starting at index i with size at most
   * j */
  Sequence substr(std::size_t i, std::size_t j) const;
  /** Return the prefix of this string of size at most i */
  Sequence prefix(std::size_t i) const { return substr(0, i); }
  /** Return the suffix of this string of size at most i */
  Sequence suffix(std::size_t i) const { return substr(size() - i, i); }

  /**
   * Checks if there is any overlap between this string and another string. This
   * corresponds to checking whether one string contains the other and whether a
   * substring of one is a prefix of the other and vice-versa.
   *
   * @param y The other string
   * @return True if there is an overlap, false otherwise
   */
  bool noOverlapWith(const Sequence& y) const;

  /** string overlap
   *
   * if overlap returns m>0,
   * then the maximal suffix of this string that is a prefix of y is of length
   * m.
   *
   * For example, if x is "abcdef", then:
   * x.overlap("defg") = 3
   * x.overlap("ab") = 0
   * x.overlap("d") = 0
   * x.overlap("bcdefdef") = 5
   */
  std::size_t overlap(const Sequence& y) const;
  /** string reverse overlap
   *
   * if roverlap returns m>0,
   * then the maximal prefix of this string that is a suffix of y is of length
   * m.
   *
   * For example, if x is "abcdef", then:
   * x.roverlap("aaabc") = 3
   * x.roverlap("def") = 0
   * x.roverlap("d") = 0
   * x.roverlap("defabcde") = 5
   *
   * Notice that x.overlap(y) = y.roverlap(x)
   */
  std::size_t roverlap(const Sequence& y) const;

  /** get the internal Node representation of this string */
  const std::vector<Node>& getVec() const { return d_seq; }
  /** get the internal unsigned value of the first character in this string */
  Node front() const;
  /** get the internal unsigned value of the last character in this string */
  Node back() const;
  /**
   * Returns the maximum length of string representable by this class.
   * Corresponds to the maximum size of d_seq.
   */
  static size_t maxSize();

 private:
  /**
   * Returns a negative number if *this < y, 0 if *this and y are equal and a
   * positive number if *this > y.
   */
  int cmp(const Sequence& y) const;
  /** The element type of the sequence */
  TypeNode d_type;
  /** The data of the sequence */
  std::vector<Node> d_seq;
}; /* class Sequence */

namespace strings {


struct CVC4_PUBLIC SequenceHashFunction {
size_t operator()(const ::CVC4::Sequence& s) const {
  return std::hash<std::vector<Node>>()(s.getVec());
}
}; /* struct SequenceHashFunction */

}  // namespace strings

std::ostream& operator<<(std::ostream& os, const Sequence& s) CVC4_PUBLIC;

}  // namespace CVC4

#endif /* CVC4__EXPR__SEQUENCE_H */
