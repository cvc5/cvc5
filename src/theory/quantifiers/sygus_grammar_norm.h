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

#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SygusGrammarNorm;

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
class TypeObject
{
 public:
  /* TODO fix doc */
  /* Creates an unresolved type and datatype with the given name. These will be
   * used for the normalization of the given type node */
  TypeObject(TypeNode src_tn, TypeNode unres_tn);
  ~TypeObject() {}

  // original

  /* The original typenode this TypeObject is built from */
  TypeNode d_tn;
  // -------------------------------

  // info to build normalized type node

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
  /* Datatype to represent type's structure */
  Datatype d_dt;
}; /* class TypeObject */

/** Operator position trie class
 *
 * This data structure stores an unresolved type corresponding to the
 * normalization of a type. This unresolved type is indexed by the positions of
 * the construtors of the datatype associated with the original type. The list
 * of positions represent the operators, associated with the respective
 * considered constructors, that were used for building the unresolved type.
 *
 * Example:
 *
 * Let A be a type defined by the grammar "A -> x | 0 | 1 | A + A". In its
 * datatype representation the operator for "x" is in position 0, for "0" in
 * position "1" and so on. Consider entries (T, [op_1, ..., op_n]) -> T' to
 * represent that a type T is normalized with operators [op_1, ..., op_n] into
 * the type T'. For entries
 *
 * (A, [x, 0, 1, +]) -> A1
 * (A, [x, 1, +]) -> A2
 * (A, [1, +]) -> A3
 * (A, [0]) -> AZ
 * (A, [x]) -> AX
 * (A, [1]) -> AO
 *
 * the OpPosTrie T we build for this type is :
 *
 * T[A] :
 *      T[A].d_children[0] : AX
 *        T[A].d_children[0].d_children[1] :
 *          T[A].d_children[0].d_children[1].d_children[2] :
 *            T[A].d_children[0].d_children[1].d_children[2].d_children[3] : A1
 *        T[A].d_children[0].d_children[2] :
 *          T[A].d_children[0].d_children[2].d_children[3] : A2
 *      T[A].d_children[1] : AZ
 *      T[A].d_children[2] : AO
 *        T[A].d_children[2].d_children[4] : A3
 *
 * Nodes store the types built for the path of positions up to that point, if any.
 */
class OpPosTrie
{
 public:
  /** type retrieval/addition
   *
   * if type indexed by the given operator positions is already in the trie then
   * unres_t becomes the indexed type and true is returned. Otherwise a new type
   * is created, indexed by the given positions, and assigned to unres_t, with
   * false being returned.
   */
  bool getOrMakeType(TypeNode tn,
                     TypeNode& unres_tn,
                     std::vector<unsigned> op_pos,
                     unsigned ind = 0);
  /** clear all data from this trie */
  void clear() { d_children.clear(); }
 private:
  /** the data (only set for the final node of an inserted path) */
  TypeNode d_unres_tn;
  /* the children of the trie node */
  std::map<unsigned, OpPosTrie> d_children;
}; /* class TermArgTrie */

class Strat
{
 public:
  virtual void buildType(SygusGrammarNorm* sygus_norm,
                         TypeObject& to,
                         const Datatype& dt,
                         std::vector<unsigned>& op_pos) = 0;
}; /* class Strat */

class StratChain : public Strat
{
 private:
  unsigned d_chain_op_pos;
  std::vector<unsigned> d_elem_pos;

 public:
  StratChain(unsigned chain_op_pos, std::vector<unsigned> elem_pos)
      : d_chain_op_pos(chain_op_pos), d_elem_pos(elem_pos){};

  virtual void buildType(SygusGrammarNorm* sygus_norm,
                         TypeObject& to,
                         const Datatype& dt,
                         std::vector<unsigned>& op_pos) override;

  enum Block
  {
    OP,
    ELEMS_ID
  };

  static std::map<TypeNode, std::map<Block, Node>> d_assoc;
  static inline void addType(TypeNode tn, std::map<Block, Node> assoc)
  {
    if (d_assoc.find(tn) == d_assoc.end())
    {
      d_assoc[tn] = assoc;
    }
  }
}; /* class StratChain */

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

  TypeNode normalizeSygusRec(TypeNode tn);

  /* recursion depth is limited by the height of the types, which is small  */
  TypeNode normalizeSygusRec(TypeNode tn,
                             const Datatype& dt,
                             std::vector<unsigned> op_pos);
  /** reference to current node manager */
  NodeManager* d_nm;
  /** reference to smt engine */
  SmtEngine* d_smte;
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** sygus term database associated with this utility */
  TermDbSygus* d_tds;

 private:
  /** List of variable inputs of function being synthesized.
   *
   * This information is needed in the construction of each datatype
   * representation of type nodes contained in the type node being normalized
   */
  TNode d_sygus_vars;
  /* Datatypes to be resolved */
  std::vector<Datatype> d_dt_all;
  /* Types to be resolved */
  std::set<Type> d_unres_t_all;

  /* Associates type nodes with OpPosTries */
  std::map<TypeNode, OpPosTrie> d_tries;
  /* For each type node associates operators with their positions in the cons
   * list */
  std::map<TypeNode, std::map<Node, unsigned>> d_tn_to_op_to_pos;

  enum
  {
    OP_PLUS,          // collect plus
    OP_MINUS,         // collect minus
    VARS,             // collect variables
    CONST_ZERO,       // collect 0
    CONST_ONE,        // collect 1
    NON_ZERO_CONSTS,  // collect numbers and ITEs
    A_VAR,            // collect any variable
    A_NON_ZERO_CONST  // collect any number or ITE
  };

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
                         const Datatype& dt);

  Strat* inferStrategy(const Datatype& dt, std::vector<unsigned>& op_pos);

  void addConsInfo(TypeObject& to, const DatatypeConstructor& cons);

  void buildDatatype(TypeObject& to, const Datatype& dt);

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
