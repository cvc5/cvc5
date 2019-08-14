/*********************                                                        */
/*! \file type_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus type info data structure
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__TYPE_INFO_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__TYPE_INFO_H

#include <map>
#include <unordered_set>

#include "expr/node.h"
#include "theory/quantifiers/sygus/type_node_id_trie.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDbSygus;

/**
 * This data structure stores statically computed information regarding a sygus
 * datatype type.
 *
 * To use an instance of this class x, call x.initialize(tn); where tn is a
 * sygus datatype type. Then, most of the query methods on x can be called.
 * As an exception, the variable subclass queries require that additionally
 * x.initializeVarSubclasses() is called.
 *
 */
class SygusTypeInfo
{
 public:
  SygusTypeInfo();
  //-------------------------------------------- initialize
  /** initialize this information for sygus datatype type tn */
  void initialize(TermDbSygus* tds, TypeNode tn);
  /**
   * Initialize the variable subclass information for this class. Must have
   * called initialize(...) prior to calling this method.
   */
  void initializeVarSubclasses();
  //-------------------------------------------- end initialize
  /** Get the builtin type that this sygus type encodes */
  TypeNode getBuiltinType() const;
  /** Get the variable list (formal argument list) for the sygus type */
  const std::vector<Node>& getVarList() const;
  /**
   * Return the index of the constructor of this sygus type that encodes
   * application of the builtin Kind k, or -1 if one does not exist.
   */
  int getKindConsNum(Kind k) const;
  /**
   * Return the index of the constructor of this sygus type that encodes
   * constant c, or -1 if one does not exist.
   */
  int getConstConsNum(Node c) const;
  /**
   * Return the index of the constructor of this sygus type whose builtin
   * operator is n, or -1 if one does not exist.
   */
  int getOpConsNum(Node n) const;
  /** Is there a constructor that encodes application of builtin Kind k? */
  bool hasKind(Kind k) const;
  /** Is there a constructor that encodes constant c? */
  bool hasConst(Node c) const;
  /** Is there a constructor whose builtin operator is n? */
  bool hasOp(Node n) const;
  /**
   * Returns true if this sygus type has a constructor whose sygus operator is
   * ITE, or is a lambda whose body is ITE.
   */
  bool hasIte() const;
  /**
   * Get the builtin kind for the i^th constructor of this sygus type. If the
   * i^th constructor does not encode an application of a builtin kind, this
   * method returns UNDEFINED_KIND.
   */
  Kind getConsNumKind(unsigned i) const;
  /**
   * Get the construct for the i^th constructor of this sygus type. If the
   * i^th constructor does not encode a builtin constant, this method returns
   * the null node.
   */
  Node getConsNumConst(unsigned i) const;
  /** Get the builtin operator of the i^th constructor of this sygus type */
  Node getConsNumOp(unsigned i) const;
  /**
   * Returns true if the i^th constructor encodes application of a builtin Kind.
   */
  bool isKindArg(unsigned i) const;
  /**
   * Returns true if the i^th constructor encodes a builtin constant.
   */
  bool isConstArg(unsigned i) const;
  /**
   * Get the index of the "any constant" constructor of type tn if it has one,
   * or returns -1 otherwise.
   */
  int getAnyConstantConsNum() const;
  /** has subterm symbolic constructor
   *
   * Returns true if any subterm of type tn can be a symbolic constructor.
   */
  bool hasSubtermSymbolicCons() const;
  /** get subfield types
   *
   * This adds all "subfield types" of tn to sf_types. A type tnc is a subfield
   * type of tn if there exists a selector chain S1( ... Sn( x )...) that has
   * type tnc, where x has type tn. In other words, tnc is the type of some
   * subfield of terms of type tn, at any depth.
   */
  void getSubfieldTypes(std::vector<TypeNode>& sf_types) const;
  //--------------------------------- variable subclasses
  /** Get subclass id for variable
   *
   * This returns the "subclass" identifier for variable v in sygus
   * type tn. A subclass identifier groups variables based on the sygus
   * types they occur in:
   *   A -> A + B | C + C | x | y | z | w | u
   *   B -> y | z
   *   C -> u
   * The variables in this grammar can be grouped according to the sygus types
   * they appear in:
   *   { x,w } occur in A
   *   { y,z } occur in A,B
   *   { u } occurs in A,C
   * We say that e.g. x, w are in the same subclass.
   *
   * If this method returns 0, then v is not a variable in sygus type tn.
   * Otherwise, this method returns a positive value n, such that
   * getSubclassIdForVar[v1] = getSubclassIdForVar[v2] iff v1 and v2 are in the
   * same subclass.
   *
   * The type tn should be the type of an enumerator registered to this
   * database, where notice that we do not compute this information for the
   * subfield types of the enumerator.
   */
  unsigned getSubclassForVar(Node v) const;
  /**
   * Get the number of variable in the subclass with identifier sc for type tn.
   */
  unsigned getNumSubclassVars(unsigned sc) const;
  /** Get the i^th variable in the subclass with identifier sc for type tn */
  Node getVarSubclassIndex(unsigned sc, unsigned i) const;
  /**
   * Get the a variable's index in its subclass list. This method returns true
   * iff variable v has been assigned a subclass in tn. It updates index to
   * be v's index iff the method returns true.
   */
  bool getIndexInSubclassForVar(Node v, unsigned& index) const;
  /**
   * Are the variable subclasses a trivial partition (each variable subclass
   * has a single variable)?
   */
  bool isSubclassVarTrivial() const;
  //--------------------------------- end variable subclasses
  /**
   * Get the minimum depth of type in this grammar
   *
   */
  unsigned getMinTypeDepth(TypeNode tn) const;
  /** Get the minimum size for a term of this sygus type */
  unsigned getMinTermSize() const;
  /**
   * Get the minimum size for a term that is an application of a constructor of
   * this type.
   */
  unsigned getMinConsTermSize(unsigned cindex);

 private:
  /** The sygus type that this class is for */
  TypeNode d_this;
  /** The builtin type that this sygus type encodes */
  TypeNode d_btype;
  /** The variable list of the sygus type */
  std::vector<Node> d_var_list;
  /**
   * Maps constructor indices to the (builtin) Kind that they encode, if any.
   */
  std::map<unsigned, Kind> d_arg_kind;
  /** Reverse of the above map */
  std::map<Kind, unsigned> d_kinds;
  /**
   * Whether this sygus type has a constructors whose sygus operator is ITE,
   * or is a lambda whose body is ITE.
   */
  bool d_hasIte;
  /**
   * Maps constructor indices to the constant that they encode, if any.
   */
  std::map<unsigned, Node> d_arg_const;
  /** Reverse of the above map */
  std::map<Node, unsigned> d_consts;
  /**
   * Maps constructor indices to the operator they encode.
   */
  std::map<unsigned, Node> d_arg_ops;
  /** Reverse of the above map */
  std::map<Node, unsigned> d_ops;
  /**
   * This maps the subfield datatype types T to the smallest size of a term of
   * this sygus type that includes T as a subterm. For example, for type A with
   * grammar:
   *   A -> B+B | 0 | B-D
   *   B -> C+C
   *   ...
   * we have that d_min_type_depth = { A -> 0, B -> 1, C -> 2, D -> 1 }.
   */
  std::map<TypeNode, unsigned> d_min_type_depth;
  /** The minimimum size term of this type */
  unsigned d_min_term_size;
  /**
   * Maps constructors to the minimum size term that is an application of that
   * constructor.
   */
  std::map<unsigned, unsigned> d_min_cons_term_size;
  /** a cache for getSelectorWeight */
  std::map<Node, unsigned> d_sel_weight;
  /**
   * For each sygus type, the index of the "any constant" constructor, if it
   * has one, or -1 otherwise.
   */
  int d_sym_cons_any_constant;
  /**
   * Whether any subterm of this type contains a symbolic constructor. This
   * corresponds to whether sygus repair techniques will ever have any effect
   * for this type.
   */
  bool d_has_subterm_sym_cons;
  /**
   * Map from sygus types and bound variables to their type subclass id. Note
   * type class identifiers are computed for each type of registered sygus
   * enumerators, but not all sygus types. For details, see getSubclassIdForVar.
   */
  std::map<Node, unsigned> d_var_subclass_id;
  /** the list of variables with given subclass */
  std::map<unsigned, std::vector<Node> > d_var_subclass_list;
  /** the index of each variable in the above list */
  std::map<Node, unsigned> d_var_subclass_list_index;
  /** computes the map d_min_type_depth */
  void computeMinTypeDepthInternal(TypeNode root_tn, unsigned type_depth);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__TYPE_INFO_H */
