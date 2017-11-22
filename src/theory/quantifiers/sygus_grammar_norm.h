/*********************                                                        */
/*! \file sygus_grammar_norm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for simplifying SyGuS grammars after they are encoded into
 ** datatypes.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_SIMP_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_SIMP_H

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;

/** Keeps the necessary information about a sygus type:
 *
 * the original typenode, from which the datatype representation can be
 * extracted
 *
 * the operators, names and argument types for each constructor
 *
 * the unresolved type used as placeholder for references of the yet to be built
 * type
 *
 * a datatype to represent the structure of the typenode for the new type */
struct TypeObject
{
  /* Both constructors create an unresolved type and datatype with the given
   * name. An original typenode is optional, since normalized types can be
   * created from scratch during normalization */
  TypeObject(TypeNode src_tn, std::string type_name);
  TypeObject(std::string type_name);
  ~TypeObject() {}

  /* The original typenode this TypeObject is built from */
  TypeNode d_tn;
  /* The type represented by the typenode */
  Type d_t;
  /* Operators for each constructor. */
  std::vector<Expr> d_ops;
  /* Names for each constructor. */
  std::vector<std::string> d_cons_names;
  /* List of argument types for each constructor */
  std::vector<std::vector<Type>> d_cons_args_t;
  /* Unresolved type placeholder */
  Type d_unres_t;
  /* Datatype to represent type's structure */
  Datatype d_dt;
};

/** Utility for normalizing SyGuS grammars and avoid spurious enumarations
 *
 * Uses the datatype representation of a SyGuS grammar to identify entries that
 * can normalized in order to have less possible enumerations. An example is
 * with integer types, e.g.:
 *
 * Int -> x | y | Int + Int | Int - Int | 0 | 1 | ite( Bool, Int, Int ) |
 *        c1...cn
 *
 * where c1...cn are additional constants (in the case of large constants
 * appearing in the conjecture).
 *
 * becomes
 *
 * Int -> ite( Bool, Int, Int ) | IntN
 * IntN -> IntX | Int0 - IntX
 * Int0 -> 0
 * IntX -> IntXX + IntX | IntY
 * IntXX -> x
 * IntY -> IntYY + IntY | IntC
 * IntYY -> y
 * IntC -> IntCC + IntC | IntV
 * IntCC -> 1
 * IntV -> 0 | c1...cn */
class SygusGrammarNorm
{
 public:
  SygusGrammarNorm(QuantifiersEngine* qe, CegConjecture* p);
  ~SygusGrammarNorm() {}
  /** creates a normalized typenode from a given one.
   *
   * In a normalized typenode all of its types that can be normalized (e.g. Int)
   * are so and its other types are structurally identical to the original
   * typenode it normalizes.
   *
   * sygus_vars are the input variables for the function to be synthesized,
   * which are used as input for the built datatypes. */
  TypeNode normalizeSygusType(TypeNode tn, Node sygus_vars);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** parent conjecture
   *
   * This contains global information about the synthesis conjecture. */
  CegConjecture* d_parent;

  /** sygus term database associated with this utility */
  TermDbSygus* d_tds;

  /** normalize integer type
   *
   * TODO actually perform the normalization #1304
   *
   * ind is the index of the analyzed typeobject in tos
   *
   * New types created during normalization will be added to tos and
   * tn_to_unres
   *
   * sygus_vars is used as above for datatype construction */
  void normalizeSygusInt(unsigned ind,
                         std::vector<TypeObject>& tos,
                         std::map<TypeNode, Type>& tn_to_unres,
                         Node sygus_vars);

  /** Traverses the datatype representation of src_tn and collects the types it
   * contains
   *
   * For each new typenode a TypeObject is created, with an unresolved type and
   * a datatype to be later resolved and constructed, respectively. These are
   * accumulated in tos.
   *
   * tn_to_unres maps the sygus types that the typenodes stand for into
   * the unresolved type to be built for the typenodes normalizations.
   *
   * visited caches visited nodes
   */
  void collectInfoFor(TypeNode src_tn,
                      std::vector<TypeObject>& tos,
                      std::map<TypeNode, Type>& tn_to_unres,
                      std::map<TypeNode, bool>& visited);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
