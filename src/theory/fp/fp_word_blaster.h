/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Converts floating-point nodes to bit-vector expressions.
 *
 * Uses the symfpu library to convert from floating-point operations to
 * bit-vectors and propositions allowing the theory to be solved by
 * 'bit-blasting'.
 *
 * !!! This header is not to be included in any other headers !!!
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__FP_WORD_BLASTER_H
#define CVC5__THEORY__FP__FP_WORD_BLASTER_H

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "symfpu/core/unpackedFloat.h"
#include "theory/valuation.h"
#include "util/bitvector.h"
#include "util/floatingpoint_size.h"
#include "util/hash.h"

namespace cvc5::internal {
namespace theory {
namespace fp {

/**
 * This is a symfpu symbolic "back-end".  It allows the library to be used to
 * construct bit-vector expressions that compute floating-point operations.
 * This is effectively the glue between symfpu's notion of "signed bit-vector"
 * and cvc5's node.
 */
namespace symfpuSymbolic {

// Forward declarations of the wrapped types so that traits can be defined early
// and used in the implementations
class symbolicRoundingMode;
class floatingPointTypeInfo;
class symbolicProposition;
template <bool T>
class symbolicBitVector;

// This is the template parameter for symfpu's templates.
class traits
{
 public:
  // The six key types that symfpu uses.
  typedef unsigned bwt;
  typedef symbolicRoundingMode rm;
  typedef floatingPointTypeInfo fpt;
  typedef symbolicProposition prop;
  typedef symbolicBitVector<true> sbv;
  typedef symbolicBitVector<false> ubv;

  // Give concrete instances (wrapped nodes) for each rounding mode.
  static symbolicRoundingMode RNE(void);
  static symbolicRoundingMode RNA(void);
  static symbolicRoundingMode RTP(void);
  static symbolicRoundingMode RTN(void);
  static symbolicRoundingMode RTZ(void);

  // Properties used by symfpu
  static void precondition(const bool b);
  static void postcondition(const bool b);
  static void invariant(const bool b);
  static void precondition(const prop& p);
  static void postcondition(const prop& p);
  static void invariant(const prop& p);
};

// Use the same type names as symfpu.
typedef traits::bwt bwt;

/**
 * Wrap the cvc5::internal::Node types so that we can debug issues with this back-end
 */
class nodeWrapper : public Node
{
 protected:
  nodeWrapper(const Node& n) : Node(n) {}
};

class symbolicProposition : public nodeWrapper
{
 protected:
  bool checkNodeType(const TNode node);

  friend ::symfpu::ite<symbolicProposition, symbolicProposition>;  // For ITE

 public:
  symbolicProposition(const Node n);
  symbolicProposition(bool v);
  symbolicProposition(const symbolicProposition& old);

  symbolicProposition operator!(void) const;
  symbolicProposition operator&&(const symbolicProposition& op) const;
  symbolicProposition operator||(const symbolicProposition& op) const;
  symbolicProposition operator==(const symbolicProposition& op) const;
  symbolicProposition operator^(const symbolicProposition& op) const;
};

class symbolicRoundingMode : public nodeWrapper
{
 protected:
  bool checkNodeType(const TNode n);

  friend ::symfpu::ite<symbolicProposition, symbolicRoundingMode>;  // For ITE

 public:
  symbolicRoundingMode(const Node n);
  symbolicRoundingMode(const unsigned v);
  symbolicRoundingMode(const symbolicRoundingMode& old);

  symbolicProposition valid(void) const;
  symbolicProposition operator==(const symbolicRoundingMode& op) const;
};

// Type function for mapping between types
template <bool T>
struct signedToLiteralType;

template <>
struct signedToLiteralType<true>
{
  typedef int literalType;
};
template <>
struct signedToLiteralType<false>
{
  typedef unsigned int literalType;
};

template <bool isSigned>
class symbolicBitVector : public nodeWrapper
{
 protected:
  typedef typename signedToLiteralType<isSigned>::literalType literalType;

  Node boolNodeToBV(Node node) const;
  Node BVToBoolNode(Node node) const;

  Node fromProposition(Node node) const;
  Node toProposition(Node node) const;
  bool checkNodeType(const TNode n);
  friend symbolicBitVector<!isSigned>;  // To allow conversion between the types

  friend ::symfpu::ite<symbolicProposition,
                       symbolicBitVector<isSigned> >;  // For ITE

 public:
  symbolicBitVector(const Node n);
  symbolicBitVector(const bwt w, const unsigned v);
  symbolicBitVector(const symbolicProposition& p);
  symbolicBitVector(const symbolicBitVector<isSigned>& old);
  symbolicBitVector(const BitVector& old);

  bwt getWidth(void) const;

  /*** Constant creation and test ***/
  static symbolicBitVector<isSigned> one(const bwt& w);
  static symbolicBitVector<isSigned> zero(const bwt& w);
  static symbolicBitVector<isSigned> allOnes(const bwt& w);

  symbolicProposition isAllOnes() const;
  symbolicProposition isAllZeros() const;

  static symbolicBitVector<isSigned> maxValue(const bwt& w);
  static symbolicBitVector<isSigned> minValue(const bwt& w);

  /*** Operators ***/
  symbolicBitVector<isSigned> operator<<(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator>>(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator|(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator&(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator+(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator-(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator*(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator/(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator%(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> operator-(void) const;
  symbolicBitVector<isSigned> operator~(void) const;
  symbolicBitVector<isSigned> increment() const;
  symbolicBitVector<isSigned> decrement() const;
  symbolicBitVector<isSigned> signExtendRightShift(
      const symbolicBitVector<isSigned>& op) const;

  /*** Modular operations ***/
  // This back-end doesn't do any overflow checking so these are the same as
  // other operations
  symbolicBitVector<isSigned> modularLeftShift(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> modularRightShift(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> modularIncrement() const;
  symbolicBitVector<isSigned> modularDecrement() const;
  symbolicBitVector<isSigned> modularAdd(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> modularNegate() const;

  /*** Comparisons ***/
  symbolicProposition operator==(const symbolicBitVector<isSigned>& op) const;
  symbolicProposition operator<=(const symbolicBitVector<isSigned>& op) const;
  symbolicProposition operator>=(const symbolicBitVector<isSigned>& op) const;
  symbolicProposition operator<(const symbolicBitVector<isSigned>& op) const;
  symbolicProposition operator>(const symbolicBitVector<isSigned>& op) const;

  /*** Type conversion ***/
  // cvc5 nodes make no distinction between signed and unsigned, thus these are
  // trivial
  symbolicBitVector<true> toSigned(void) const;
  symbolicBitVector<false> toUnsigned(void) const;

  /*** Bit hacks ***/
  symbolicBitVector<isSigned> extend(bwt extension) const;
  symbolicBitVector<isSigned> contract(bwt reduction) const;
  symbolicBitVector<isSigned> resize(bwt newSize) const;
  symbolicBitVector<isSigned> matchWidth(
      const symbolicBitVector<isSigned>& op) const;
  symbolicBitVector<isSigned> append(
      const symbolicBitVector<isSigned>& op) const;

  // Inclusive of end points, thus if the same, extracts just one bit
  symbolicBitVector<isSigned> extract(bwt upper, bwt lower) const;
};

// Use the same type information as the literal back-end but add an interface to
// TypeNodes for convenience.
class floatingPointTypeInfo : public FloatingPointSize
{
 public:
  floatingPointTypeInfo(const TypeNode t);
  floatingPointTypeInfo(unsigned exp, unsigned sig);
  floatingPointTypeInfo(const floatingPointTypeInfo& old);

  TypeNode getTypeNode(void) const;
};
}  // namespace symfpuSymbolic

/**
 * This class uses SymFPU to convert an expression containing floating-point
 * kinds and operations into a logically equivalent form with bit-vector
 * operations replacing the floating-point ones.  It also has a getValue method
 * to produce an expression which will reconstruct the value of the
 * floating-point terms from a valuation.
 *
 * Internally it caches all of the unpacked floats so that unnecessary packing
 * and unpacking operations are avoided and to make best use of structural
 * sharing.
 */
class FpWordBlaster
{
 public:
  /** Constructor. */
  FpWordBlaster(context::UserContext*);
  /** Destructor. */
  ~FpWordBlaster();

  /** Adds a node to the conversion, returns the converted node */
  Node wordBlast(TNode);

  /**
   * Gives the node representing the value of a word-blasted variable.
   * Returns a null node if it has not been word-blasted.
   */
  Node getValue(Valuation&, TNode);

  context::CDList<Node> d_additionalAssertions;

 protected:
  typedef symfpuSymbolic::traits traits;
  typedef ::symfpu::unpackedFloat<symfpuSymbolic::traits> uf;
  typedef symfpuSymbolic::traits::rm rm;
  typedef symfpuSymbolic::traits::fpt fpt;
  typedef symfpuSymbolic::traits::prop prop;
  typedef symfpuSymbolic::traits::ubv ubv;
  typedef symfpuSymbolic::traits::sbv sbv;

  typedef context::CDHashMap<Node, uf> fpMap;
  typedef context::CDHashMap<Node, rm> rmMap;
  typedef context::CDHashMap<Node, prop> boolMap;
  typedef context::CDHashMap<Node, ubv> ubvMap;
  typedef context::CDHashMap<Node, sbv> sbvMap;

  fpMap d_fpMap;
  rmMap d_rmMap;
  boolMap d_boolMap;
  ubvMap d_ubvMap;
  sbvMap d_sbvMap;

  /* These functions take a symfpu object and convert it to a node.
   * These should ensure that constant folding it will give a
   * constant of the right type.
   */

  Node ufToNode(const fpt&, const uf&) const;
  Node rmToNode(const rm&) const;
  Node propToNode(const prop&) const;
  Node ubvToNode(const ubv&) const;
  Node sbvToNode(const sbv&) const;

  /* Creates the relevant components for a variable */
  uf buildComponents(TNode current);
};

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FP__THEORY_FP_H */
