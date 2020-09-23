/*********************                                                        */
/*! \file sygus_grammar_norm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for simplifying SyGuS grammars after they are encoded into
 ** datatypes.
 **/
#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H

#include <map>
#include <memory>
#include <string>
#include <vector>

#include "expr/node.h"
#include "expr/sygus_datatype.h"
#include "expr/type.h"
#include "expr/type_node.h"
#include "theory/quantifiers/term_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SygusGrammarNorm;
class TermDbSygus;

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
 * Nodes store the types built for the path of positions up to that point, if
 * any.
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
                     const std::vector<unsigned>& op_pos,
                     unsigned ind = 0);
  /** clear all data from this trie */
  void clear() { d_children.clear(); }

 private:
  /** the data (only set for the final node of an inserted path) */
  TypeNode d_unres_tn;
  /* the children of the trie node */
  std::map<unsigned, OpPosTrie> d_children;
}; /* class OpPosTrie */

/** Utility for normalizing SyGuS grammars to avoid spurious enumerations
 *
 * Uses the datatype representation of a SyGuS grammar to identify entries that
 * can normalized in order to have less possible enumerations. An example is
 * with integer types, e.g.:
 *
 * Int -> x | y | Int + Int | 0 | 1 | ite(Bool, Int, Int)
 *
 * becomes
 *
 * Int0 -> IntZ | Int1
 * IntZ -> 0
 * Int1 -> IntX | IntX + Int1 | Int2
 * IntX -> x
 * Int2 -> IntY | IntY + Int2 | Int3
 * IntY -> y
 * Int3 -> IntO | IntO + Int3 | Int4
 * IntO -> 1
 * Int4 -> IntITE | IntITE + Int4
 * IntITE -> ite(Bool, Int0, Int0)
 *
 * TODO: #1304 normalize more complex grammars
 *
 * This class also performs more straightforward normalizations, such as
 * expanding definitions of functions declared with a "define-fun" command.
 * These lighweight transformations are always applied, independently of the
 * normalization option being enabled.
 */
class SygusGrammarNorm
{
 public:
  SygusGrammarNorm(QuantifiersEngine* qe);
  ~SygusGrammarNorm() {}
  /** creates a normalized typenode from a given one.
   *
   * In a normalized typenode all typenodes it contains are normalized.
   * Normalized typenodes can be structurally identicial to their original
   * counterparts.
   *
   * sygus_vars are the input variables for the function to be synthesized,
   * which are used as input for the built datatypes.
   *
   * This is the function that will resolve all types and datatypes built during
   * normalization. This operation can only be performed after all types
   * contained in "tn" have been normalized, since the resolution of datatypes
   * depends on all types involved being defined.
   */
  TypeNode normalizeSygusType(TypeNode tn, Node sygus_vars);

  /* Retrives, or, if none, creates, stores and returns, the node for the
   * identity operator (\lambda x. x) for the given type node */
  static inline Node getIdOp(TypeNode tn)
  {
    auto it = d_tn_to_id.find(tn);
    if (it == d_tn_to_id.end())
    {
      std::vector<Node> vars = {NodeManager::currentNM()->mkBoundVar(tn)};
      Node n = NodeManager::currentNM()->mkNode(
          kind::LAMBDA,
          NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, vars),
          vars.back());
      d_tn_to_id[tn] = n;
      return n;
    }
    return it->second;
  }

 private:
  /** Keeps the necessary information for bulding a normalized type:
   *
   * the original typenode, from which the datatype representation can be
   * extracted
   *
   * the operators, names, print callbacks and list of argument types for each
   * constructor
   *
   * the unresolved type node used as placeholder for references of the yet to
   * be built normalized type
   *
   * A (SyGuS) datatype to represent the structure of the type node for the
   * normalized type.
   */
  class TypeObject
  {
   public:
    /* Stores the original type node and the unresolved placeholder. The
     * datatype for the latter is created with the respective name. */
    TypeObject(TypeNode src_tn, TypeNode unres_tn);
    ~TypeObject() {}

    /** adds information in "cons" (operator, name, print callback, argument
     * types) as it is into "to"
     *
     * A side effect of this procedure is to expand the definitions in the sygus
     * operator of "cons"
     *
     * The types of the arguments of "cons" are recursively normalized
     */
    void addConsInfo(SygusGrammarNorm* sygus_norm,
                     const DTypeConstructor& cons);

    /** initializes a datatype with the information in the type object
     *
     * "dt" is the datatype of the original typenode. It is necessary for
     * retrieving ancillary information during the datatype building, such as
     * its sygus type (e.g. Int)
     *
     * The initialized datatype and its unresolved type are saved in the global
     * accumulators of "sygus_norm"
     */
    void initializeDatatype(SygusGrammarNorm* sygus_norm, const DType& dt);

    //---------- information stored from original type node

    /* The original typenode this TypeObject is built from */
    TypeNode d_tn;

    //---------- information to build normalized type node

    /* Unresolved type node placeholder */
    TypeNode d_unres_tn;
    /** A sygus datatype */
    SygusDatatype d_sdt;
  }; /* class TypeObject */

  /** Transformation abstract class
   *
   * Classes extending this one will define specif transformationst for building
   * normalized types based on applications of specific operators
   */
  class Transf
  {
   public:
    virtual ~Transf() {}

    /** abstract function for building normalized types
     *
     * Builds normalized types for the operators specifed by the positions in
     * op_pos of constructors from dt. The built types are associated with the
     * given type object and accumulated in the sygus_norm object, whose
     * utilities for any extra necessary normalization.
     */
    virtual void buildType(SygusGrammarNorm* sygus_norm,
                           TypeObject& to,
                           const DType& dt,
                           std::vector<unsigned>& op_pos) = 0;
  }; /* class Transf */

  /** Drop transformation class
   *
   * This class builds a type by dropping a set of redundant constructors,
   * whose indices are given as input to the constructor of this class.
   */
  class TransfDrop : public Transf
  {
   public:
    TransfDrop(const std::vector<unsigned>& indices) : d_drop_indices(indices)
    {
    }
    /** build type */
    void buildType(SygusGrammarNorm* sygus_norm,
                   TypeObject& to,
                   const DType& dt,
                   std::vector<unsigned>& op_pos) override;

   private:
    std::vector<unsigned> d_drop_indices;
  };

  /** Chain transformation class
   *
   * Determines how to build normalized types by chaining the application of one
   * of its operators. The resulting type should admit the same terms as the
   * previous one modulo commutativity, associativity and identity of the
   * neutral element.
   *
   * TODO: #1304:
   * - define this transformation for more than just PLUS for Int.
   * - improve the building such that elements that should not be entitled a
   * "link in the chain" (such as 5 in opposition to variables and 1) do not get
   * one
   * - consider the case when operator is applied to different types, e.g.:
   *   A -> B + B | x; B -> 0 | 1
   * - consider the case in which in which the operator occurs nested in an
   *   argument type of itself, e.g.:
   *   A -> (B + B) + B | x; B -> 0 | 1
   */
  class TransfChain : public Transf
  {
   public:
    TransfChain(unsigned chain_op_pos, const std::vector<unsigned>& elem_pos)
        : d_chain_op_pos(chain_op_pos), d_elem_pos(elem_pos){};

    /** builds types encoding a chain in which each link contains a repetition
     * of the application of the chain operator over a non-identity element
     *
     * Example: when considering, over the integers, the operator "+" and the
     * elemenst "1", "x" and "y", the built chain is e.g.
     *
     * x + ... + x + y + ... + y + 1 + ...+ 1
     *
     * whose encoding in types would be e.g.
     *
     * A  -> AX | AX + A | B
     * AX -> x
     * B  -> BY | BY + B | C
     * BY -> y
     * C  -> C1 | C1 + C
     * C1 -> 1
     *
     * ++++++++
     *
     * The types composing links in the chain are built recursively by invoking
     * sygus_norm, which caches results and handles the global normalization, on
     * the operators not used in a given link, which will lead to recalling this
     * transformation and so on until all operators originally given are
     * considered.
     */
    void buildType(SygusGrammarNorm* sygus_norm,
                   TypeObject& to,
                   const DType& dt,
                   std::vector<unsigned>& op_pos) override;

    /** Whether operator is chainable for the type (e.g. PLUS for Int)
     *
     *  Since the map this function depends on cannot be built statically, this
     *  function first build maps the first time a type is checked. As a
     *  consequence the list of chainabel operators is hardcoded in the map
     *  building.
     *
     * TODO: #1304: Cover more types and operators, make this robust to more
     * complex grammars
     */
    static bool isChainable(TypeNode tn, Node op);
    /* Whether n is the identity for the chain operator of the type (e.g. 1 is
     * not the identity 0 for PLUS for Int)
     *
     * TODO: #1304: Cover more types, make this robust to more complex grammars
     */
    static bool isId(TypeNode tn, Node op, Node n);

   private:
    /* TODO #1304: this should admit more than one, as well as which elements
     * are associated with which operator */
    /* Position of chain operator */
    unsigned d_chain_op_pos;
    /* Positions (of constructors in the datatype whose type is being
     * normalized) of elements the chain operator is applied to */
    std::vector<unsigned> d_elem_pos;
    /** Specifies for each type node which are its chainable operators
     *
     * For example, for Int the map is {OP -> [+]}
     *
     * TODO #1304: consider more operators
     */
    static std::map<TypeNode, std::vector<Kind>> d_chain_ops;
    /** Specifies for each type node and chainable operator its identity
     *
     * For example, for Int and PLUS the map is {Int -> {+ -> 0}}
     *
     * TODO #1304: consider more operators
     */
    static std::map<TypeNode, std::map<Kind, Node>> d_chain_op_id;

  }; /* class TransfChain */

  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** sygus term database associated with this utility */
  TermDbSygus* d_tds;
  /** List of variable inputs of function-to-synthesize.
   *
   * This information is needed in the construction of each datatype
   * representation of type nodes contained in the type node being normalized
   */
  TNode d_sygus_vars;
  /* Datatypes to be resolved */
  std::vector<DType> d_dt_all;
  /* Types to be resolved */
  std::set<TypeNode> d_unres_t_all;
  /* Associates type nodes with OpPosTries */
  std::map<TypeNode, OpPosTrie> d_tries;
  /* Map of type nodes into their identity operators (\lambda x. x) */
  static std::map<TypeNode, Node> d_tn_to_id;

  /** recursively traverses a typenode normalizing all of its elements
   *
   * "tn" is the typenode to be normalized
   * "dt" is its datatype representation
   * "op_pos" is the list of positions of construtors of dt that are being
   * considered for the normalization
   *
   * The result of normalizing tn with the respective constructors is cached
   * with an OpPosTrie. New types and datatypes created during normalization are
   * accumulated grobally to be later resolved.
   *
   * The normalization occurs following some inferred transformation based on
   * the sygus type (e.g. Int) of tn, and the operators being considered.
   *
   * Example: Let A be the type node encoding the grammar
   *
   * Int -> x | y | Int + Int | 0 | 1 | ite(Bool, Int, Int)
   *
   * and assume all its datatype constructors are being used for
   * normalization. The inferred normalization transformation will consider the
   * non-zero elements {x, y, 1, ite(...)} and the operator {+} to build a chain
   * of monomials, as seen above. The operator for "0" is rebuilt as is (the
   * default behaviour of operators not selected for transformations).
   *
   * recursion depth is limited by the height of the types, which is small
   */
  TypeNode normalizeSygusRec(TypeNode tn,
                             const DType& dt,
                             std::vector<unsigned>& op_pos);

  /** wrapper for the above function
   *
   * invoked when all operators of "tn" are to be considered for normalization
   */
  TypeNode normalizeSygusRec(TypeNode tn);

  /** infers a transformation for normalizing dt when allowed to use the
   * operators in the positions op_pos.
   *
   * TODO: #1304: Infer more complex transformations
   */
  std::unique_ptr<Transf> inferTransf(TypeNode tn,
                                      const DType& dt,
                                      const std::vector<unsigned>& op_pos);
}; /* class SygusGrammarNorm */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
