/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple substitution utility.
 */

#ifndef CVC5__EXPR__SUBS_H
#define CVC5__EXPR__SUBS_H

#include <map>
#include <vector>
#include "expr/node.h"

namespace cvc5 {

/**
 * Helper substitution class. Stores a substitution in parallel vectors
 * d_vars and d_subs, both of which may be arbitrary terms, having the same
 * types pairwise.
 *
 * Notice this class applies substitutions using Node::substitute. Furthermore,
 * it does not insist that the terms in d_vars are unique.
 */
class Subs
{
 public:
  /** Is the substitution empty? */
  bool empty() const;
  /** The size of the substitution */
  size_t size() const;
  /** Does the substitution contain v? */
  bool contains(Node v) const;
  /** Get the substitution for v if it exists, or null otherwise */
  Node getSubs(Node v) const;
  /** Add v -> k for fresh skolem of the same type as v */
  void add(Node v);
  /** Add v -> k for fresh skolem of the same type as v for each v in vs */
  void add(const std::vector<Node>& vs);
  /** Add v -> s to the substitution */
  void add(Node v, Node s);
  /** Add vs -> ss to the substitution */
  void add(const std::vector<Node>& vs, const std::vector<Node>& ss);
  /** Add eq[0] -> eq[1] to the substitution */
  void addEquality(Node eq);
  /** Append the substitution s to this */
  void append(Subs& s);
  /** Return the result of this substitution on n */
  Node apply(Node n, bool doRewrite = false) const;
  /** Return the result of the reverse of this substitution on n */
  Node rapply(Node n, bool doRewrite = false) const;
  /** Apply this substitution to all nodes in the range of s */
  void applyToRange(Subs& s, bool doRewrite = false) const;
  /** Apply the reverse of this substitution to all nodes in the range of s */
  void rapplyToRange(Subs& s, bool doRewrite = false) const;
  /** Get equality (= v s) where v -> s is the i^th position in the vectors */
  Node getEquality(size_t i) const;
  /** Convert substitution to map */
  std::map<Node, Node> toMap() const;
  /** Get string for this substitution */
  std::string toString() const;
  /** The data */
  std::vector<Node> d_vars;
  std::vector<Node> d_subs;
};

/**
 * Serializes a given substitution to the given stream.
 *
 * @param out the output stream to use
 * @param s the substitution to output to the stream
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Subs& s);

}  // namespace cvc5

#endif /* CVC5__EXPR__SUBS_H */
