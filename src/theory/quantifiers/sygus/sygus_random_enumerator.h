/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Random sygus enumerator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_RANDOM_ENUMERATOR_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_RANDOM_ENUMERATOR_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers/sygus/enum_val_generator.h"

namespace cvc5::internal {

class DTypeConstructor;

namespace theory {
namespace quantifiers {

class TermDbSygus;

using TypeConsMap =
    std::unordered_map<TypeNode,
                       std::vector<std::shared_ptr<DTypeConstructor>>>;

/** A random sygus value generator.
 *
 * This class is a random term generator for sygus conjectures. The sizes of the
 * generated terms approximate a geometric distribution with an expected size of
 * 1 / p, where p is a parameter specified by the user (defaults to 0.5).
 */
class SygusRandomEnumerator : public EnumValGenerator
{
 public:
  /** Constructor. Initializes the enumerator.
   *
   * @param tds pointer to term database sygus.
   */
  SygusRandomEnumerator(Env& env, TermDbSygus* tds)
      : EnumValGenerator(env), d_tds(tds)
  {
  }

  /** Initialize this class with enumerator `e`. */
  void initialize(Node e) override;

  /** Inform this generator that abstract value `v` was enumerated. */
  void addValue(Node v) override { d_cache.insert(v); }

  /**
   * Get next the next random (T-rewriter-unique) value.
   *
   * @return true if a new value is found and loop otherwise.
   */
  bool increment() override;

  /** @return the current term. */
  Node getCurrent() override { return d_currTerm; }

 private:
  /** Generates a random sygus term.
   *
   * S ::= 0 | x | (+ S S)
   *
   * Assuming we are provided the above grammar, we generate random terms by
   * starting with a skolem, `z0`, of the given sygus datatype type (grammar
   * non-terminal). We then flip a coin to determine whether or not we should
   * replace the skolem with a random constructor that takes arguments (`(+ S
   * S)` above). For example, if the first 2 coin flips are heads, then we will
   * replace `z0` with `(+ z1 z2)` and either `z1` or `z2` (randomly chosen)
   * with `(+ z3 z4)`. So, we will end up with either `(+ (+ z3 z4) z2)` or `(+
   * z1 (+ z3 z4))`. We keep doing so until we get a tails. At which point, we
   * replace all remaining skolems with random no-argument constructors (`0` and
   * `x` above) and return the resulting sygus term. So, if we get a tails at
   * the third flip in the previous example, then `incrementH` may return `(+ 1
   * (+ x x))`, `(+ (+ 1 1) 1)`, or any of the other 14 possible terms.
   *
   * \note If a skolem's datatype type does not have a no-argument constructor,
   * it is replaced with a ground value using `mkGroundValue` utility.
   * \note If a skolem's datatype type does not have a constructor that takes an
   * argument (e.g., `S ::= 0 | 1 | x | (+ 2 y)`), it is replaced with a random
   * no-argument constructor. So `incrementH` may return a term before getting a
   * tails.
   *
   * @return a randomly generated sygus term.
   */
  Node incrementH();

  /**
   * Returns smallest (in terms of size) term equivalent (up to rewriting) to
   * the given sygus term.
   */
  Node getMin(Node n);

  /** Pointer to term database sygus. */
  TermDbSygus* d_tds;
  /** The type to enumerate. */
  TypeNode d_tn;
  /** The current term. */
  Node d_currTerm;
  /** Cache of no-argument constructors for each sygus datatype type. */
  TypeConsMap d_noArgCons;
  /** Cache of argument constructors for each sygus datatype type. */
  TypeConsMap d_argCons;
  /** Cache of builtin terms we have enumerated so far. */
  std::unordered_set<Node> d_cache;
  /** Cache of smallest (in terms of size) term equivalent (up to rewriting)
   * to the given sygus term, per sygus datatatype type. */
  std::unordered_map<TypeNode, std::unordered_map<Node, Node>> d_minSygus;
  /** Cache of the size of a sygus term. */
  std::unordered_map<Node, unsigned> d_size;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__QUANTIFIERS__SYGUS_RANDOM_ENUMERATOR_H
