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

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H

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
  /* TODO fix doc */
  /* Creates an unresolved type and datatype with the given name. These will be
   * used for the normalization of the given type node */
  TypeObject(TypeNode src_tn, TypeNode unres_tn, Type unres_t);
  ~TypeObject() {}

  /* The original typenode this TypeObject is built from */
  TypeNode d_tn;
  /* Operators for each constructor. */
  std::vector<Node> d_ops;
  /* Names for each constructor. */
  std::vector<std::string> d_cons_names;
  /* Print callbacks for each constructor */
  std::vector<std::shared_ptr<SygusPrintCallback>> d_pc;
  /* List of argument types for each constructor */
  std::vector<std::vector<Type>> d_cons_args_t;
  /* Unresolved type node placeholder */
  TypeNode d_unres_tn;
  /* Unresolved type placeholder */
  Type d_unres_t;
  /* Datatype to represent type's structure */
  Datatype d_dt;
};

/** Type operators trie class
 *
 * This data structure stores a type, indexed by operators used in its
 * constructors
 *
 * For example, consider the entries
 *
 * (A, {x, 0, 1, +}) -> A1
 * (A, {x}) -> AX
 * (A, {0}) -> AZ
 * (A, {1}) -> AO
 *
 * and the order x < 0 < 1 < + for operators. The TypeOpTrie T we build for this
 * type is :
 *
 * T[A] :
 *      T[A].d_data[1] :
 *        T[A].d_data[1].d_data[1] :
 *          T[A].d_data[1].d_data[1].d_data[1] :
 *            T[A].d_data[1].d_data[1].d_data[1].d_data[1] : A1
 *        T[A].d_data[1].d_data[0] :
 *          T[A].d_data[1].d_data[0].d_data[0] :
 *            T[A].d_data[1].d_data[0].d_data[0].d_data[0] : AX
 *      T[A].d_data[0] :
 *        T[A].d_data[0].d_data[1] :
 *          T[A].d_data[0].d_data[1].d_data[0] :
 *            T[A].d_data[0].d_data[1].d_data[0].d_data[0] : AZ
 *        T[A].d_data[0].d_data[0] :
 *          T[A].d_data[0].d_data[0].d_data[1] :
 *            T[A].d_data[0].d_data[0].d_data[1].d_data[0] : AO
 *
 * Leaf nodes store the types that are indexed by the type and operator flags,
 * for example type AZ is indexed by the type A and operator flags (0, 1, 0, 0),
 * and is stored as a the (single) key in the data of
 * T[A].d_data[0].d_data[1].d_data[0].d_data[0]
 */
class TypeOpTrie
{
 public:
  /** type retrieval/addition
   *
   * if type indexed by the given operators is already in the trie then unres_t
   * becomes the indexed type and true is returned. Otherwise a new type is
   * created, indexed by the given ops, and assigned to unres_t, with false
   * being returned.
   */
  bool getOrMakeType(TypeNode tn,
                     TypeNode& unres_tn,
                     std::vector<bool> op_flags,
                     unsigned ind = 0);
  /** clear all data from this trie */
  void clear() { d_children.clear(); }

 private:
  /** the data (only set for leafs) */
  TypeNode d_unres_tn;
  /* the children of the trie node */
  std::map<bool, TypeOpTrie> d_children;
}; /* class TermArgTrie */

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
 * IntN -> IntX | Int0 | Int0 - IntX
 * Int0 -> 0
 * IntX -> IntXX | IntXX + IntX | IntY
 * IntXX -> x
 * IntY -> IntYY | IntYY + IntY | IntC
 * IntYY -> y
 * IntC -> Int1 | Int1 + IntC | IntCC
 * Int1 -> 1
 * IntCC -> c1...cn */
class SygusGrammarNorm
{
 public:
  SygusGrammarNorm(QuantifiersEngine* qe);
  ~SygusGrammarNorm() {}
  /** creates a normalized typenode from a given one.
   *
   * In a normalized typenode all of its types that can be normalized (e.g. Int)
   * are so and its other types are structurally identical to the original
   * typenode it normalizes.
   *
   * sygus_vars are the input variables for the function to be synthesized,
   * which are used as input for the built datatypes.
   */
  TypeNode normalizeSygusType(TypeNode tn, Node sygus_vars);

 private:
  /** reference to current node manager */
  NodeManager* d_nm;
  /** reference to smt engine */
  SmtEngine* d_smte;
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** sygus term database associated with this utility */
  TermDbSygus* d_tds;

  /* Datatypes to be resolved */
  std::vector<Datatype> d_dt_all;
  /* Types to be resolved */
  std::set<Type> d_unres_t_all;

  /* Caches types of type nodes to avoid recomputing types */
  std::map<TypeNode, Type> d_tn_to_t;
  /* Associates type nodes with TypeOpTries */
  std::map<TypeNode, TypeOpTrie> d_tries;
  /* For each type node associates operators with their positions in the cons list */
  std::map<TypeNode, std::map<Node, unsigned>> d_tn_to_op_to_pos;

  /* Types that can be normalized and are cached to avoid building types */
  const Type& d_int_type = NodeManager::currentNM()->integerType().toType();

  /* Simplifying (Int, {x, 0, 1, +})
   *
   * A -> x | 0 | 1 | A + A
   *
   * becomes
   *
   * A1 -> A2 | AZ
   * AZ -> 0
   * A2 -> AX | AX + A2 | A3
   * AX -> x
   * A3 -> AY | AY + A3 | A4
   * AY -> y
   * A4 -> AO | AO + A4
   * AO -> 1
   */

  /** normalize integer type
   *
   * Perform aggressive normalization of integer types: the grammar does not
   * allow the derivation of distinct terms that are equivalent w.r.t.
   * - commutativity of + and -
   * - associativity of + and -
   * - neutral element of - and +
   *
   * ind is the index of the analyzed typeobject in tos
   *
   * New types created during normalization will be added to tos and
   * tn_to_unres
   *
   * dt is the datatype of the typenode being normalized
   * sygus_vars is used as above for datatype construction
   */
  void normalizeSygusInt(unsigned ind,
                         std::vector<TypeObject>& tos,
                         std::map<TypeNode, Type>& tn_to_unres,
                         const Datatype& dt,
                         Node sygus_vars);

  TypeNode normalizeSygusRec(TypeNode tn, Node sygus_vars);

  /* recursion depth is limited by the height of the types, which is small  */
  TypeNode normalizeSygusRec(TypeNode tn,
                             const Datatype& dt,
                             std::vector<unsigned> op_pos,
                             Node sygus_vars);

  std::vector<bool> get_op_flags(std::vector<unsigned> ops, unsigned num_cons);

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
