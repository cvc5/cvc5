/*********************                                                        */
/*! \file sequence.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The sequence data type.
 **/

#include "cvc4_public.h"

#ifndef CVC4__EXPR__SEQUENCE_H
#define CVC4__EXPR__SEQUENCE_H

#include <memory>
#include <vector>

namespace CVC4 {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
class TypeNode;

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
  explicit Sequence(const TypeNode& t, const std::vector<Node>& s);
  Sequence(const Sequence& seq);

  ~Sequence();

  Sequence& operator=(const Sequence& y);

  Sequence concat(const Sequence& other) const;

  bool operator==(const Sequence& y) const { return cmp(y) == 0; }
  bool operator!=(const Sequence& y) const { return cmp(y) != 0; }
  bool operator<(const Sequence& y) const { return cmp(y) < 0; }
  bool operator>(const Sequence& y) const { return cmp(y) > 0; }
  bool operator<=(const Sequence& y) const { return cmp(y) <= 0; }
  bool operator>=(const Sequence& y) const { return cmp(y) >= 0; }

  bool strncmp(const Sequence& y, size_t n) const;
  bool rstrncmp(const Sequence& y, size_t n) const;

  /** is this the empty sequence? */
  bool empty() const;
  /** is less than or equal to sequence y */
  bool isLeq(const Sequence& y) const;
  /** Return the length of the sequence */
  size_t size() const;

  /** Return true if this sequence is a repetition of the same element */
  bool isRepeated() const;

  /**
   * Return the first position y occurs in this sequence, or std::string::npos
   * otherwise.
   */
  size_t find(const Sequence& y, size_t start = 0) const;
  /**
   * Return the first position y occurs in this sequence searching from the end,
   * or std::string::npos otherwise.
   */
  size_t rfind(const Sequence& y, size_t start = 0) const;
  /** Returns true if y is a prefix of this */
  bool hasPrefix(const Sequence& y) const;
  /** Returns true if y is a suffix of this */
  bool hasSuffix(const Sequence& y) const;
  /** Replace the character at index i in this sequence with t */
  Sequence update(size_t i, const Sequence& t) const;
  /** Replace the first occurrence of s in this sequence with t */
  Sequence replace(const Sequence& s, const Sequence& t) const;
  /** Return the subsequence of this sequence starting at index i */
  Sequence substr(size_t i) const;
  /**
   * Return the subsequence of this sequence starting at index i with size at
   * most j.
   */
  Sequence substr(size_t i, size_t j) const;
  /** Return the prefix of this sequence of size at most i */
  Sequence prefix(size_t i) const { return substr(0, i); }
  /** Return the suffix of this sequence of size at most i */
  Sequence suffix(size_t i) const { return substr(size() - i, i); }

  /**
   * Checks if there is any overlap between this sequence and another sequence.
   * This corresponds to checking whether one sequence contains the other and
   * whether a subsequence of one is a prefix of the other and vice-versa.
   *
   * @param y The other sequence
   * @return True if there is an overlap, false otherwise
   */
  bool noOverlapWith(const Sequence& y) const;

  /** sequence overlap
   *
   * if overlap returns m>0,
   * then the maximal suffix of this sequence that is a prefix of y is of length
   * m.
   *
   * For example, if x is "abcdef", then:
   * x.overlap("defg") = 3
   * x.overlap("ab") = 0
   * x.overlap("d") = 0
   * x.overlap("bcdefdef") = 5
   */
  size_t overlap(const Sequence& y) const;
  /** sequence reverse overlap
   *
   * if roverlap returns m>0,
   * then the maximal prefix of this sequence that is a suffix of y is of length
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
  size_t roverlap(const Sequence& y) const;

  /** get the element type of the sequence */
  const TypeNode& getType() const;
  /** get the internal Node representation of this sequence */
  const std::vector<Node>& getVec() const;
  /** get the internal node value of the first element in this sequence */
  const Node& front() const;
  /** get the internal node value of the last element in this sequence */
  const Node& back() const;
  /** @return The element at the i-th position */
  const Node& nth(size_t i) const;
  /**
   * Returns the maximum sequence length representable by this class.
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
  std::unique_ptr<TypeNode> d_type;
  /** The data of the sequence */
  std::vector<Node> d_seq;
};

struct SequenceHashFunction
{
  size_t operator()(const Sequence& s) const;
};

std::ostream& operator<<(std::ostream& os, const Sequence& s);

}  // namespace CVC4

#endif /* CVC4__EXPR__SEQUENCE_H */
