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
 * Implementation of LFSC node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_NODE_CONVERTER_H
#define CVC4__PROOF__LFSC__LFSC_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace proof {

/**
 * This is a helper class for the LFSC printer that converts nodes into
 * form that LFSC expects. It should only be used by the LFSC printer.
 */
class LfscNodeConverter : public NodeConverter
{
 public:
  LfscNodeConverter();
  ~LfscNodeConverter() {}
  /** convert at pre-order traversal */
  Node preConvert(Node n) override;
  /** convert at post-order traversal */
  Node postConvert(Node n) override;
  /** convert type at post-order traversal */
  TypeNode postConvertType(TypeNode tn) override;
  /**
   * Get the null terminator for kind k and type tn. The type tn can be
   * omitted if applications of kind k do not have parametric type.
   *
   * The returned null terminator is *not* converted to internal form.
   *
   * For examples of null terminators, see nary_term_utils.h.
   */
  Node getNullTerminator(Kind k, TypeNode tn = TypeNode::null());
  /**
   * Return the properly named operator for n of the form (f t1 ... tn), where
   * f could be interpreted or uninterpreted.  This method is used for cases
   * where it is important to get the term corresponding to the operator for
   * a term. An example is for the base REFL step of nested CONG.
   */
  Node getOperatorOfTerm(Node n, bool macroApply = false);
  /**
   * Recall that (forall ((x Int)) (P x)) is printed as:
   *   (apply (forall N Int) (apply P (bvar N Int)))
   * in LFSC, where N is an integer indicating the id of the variable.
   *
   * Get closure operator. In the above example, this method returns the
   * uninterpreted function whose name is "forall" and is used to construct
   * higher-order operators for each bound variable in the closure.
   *
   * To ensure typing is correct on converted terms, lambdas require further
   * care on inner variables. For example:
   *   (lambda ((x Int) (y Int) (z Int)) 0)
   * is printed as:
   *   (apply (lambda N1 Int) (apply (lambda N2 Int) (apply (lambda N3 Int) 0)))
   * The inner two lambda operators we give type
   *   (-> Sort Int Int Int)
   * We call these "partial". Then, the outer lambda is given type:
   *   (-> Sort Int Int (-> Int Int Int Int))
   */
  Node getOperatorOfClosure(Node q,
                            bool macroApply = false,
                            bool isPartial = false);
  /**
   * Get closure operator, where cop is the term returned by
   * getOperatorOfClosure(q), where q is the closures to which v
   * belongs. For example, for FORALL closures, this method will return the
   * node that prints as "(forall N Int)".
   */
  Node getOperatorOfBoundVar(Node cop, Node v);
  /**
   * Get the variable index for variable v, or assign a fresh index if it is
   * not yet assigned.
   */
  size_t getOrAssignIndexForVar(Node v);
  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalSymbol(const std::string& name, TypeNode tn);
  /**
   * Get builtin kind for internal symbol op
   */
  Kind getBuiltinKindForInternalSymbol(Node op) const;

  /** get name for user name */
  static std::string getNameForUserName(const std::string& name);
  /** get name for the name of node v, where v should be a variable */
  static std::string getNameForUserNameOf(Node v);

 private:
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /**
   * Make skolem function, if k was constructed by a skolem function identifier
   * (in SkolemManager::mkSkolemFunction) that is supported in the LFSC
   * signature.
   */
  Node maybeMkSkolemFun(Node k, bool macroApply = false);
  /**
   * Type as node, returns a node that prints in the form that LFSC will
   * interpret as the type tni. This method is required since types can be
   * passed as arguments to terms. This method assumes that tni has been
   * converted to internal form (via the convertType method of this class).
   */
  Node typeAsNode(TypeNode tni) const;
  /**
   * Get symbol for term, a special case of the method below for the type and
   * kind of n.
   */
  Node getSymbolInternalFor(Node n, const std::string& name);
  /**
   * Get symbol internal, (k,tn,name) are for caching, name is the name. This
   * method returns a fresh symbol of the given name and type. It is frequently
   * used when the type of a native operator does not match the type of the
   * LFSC operator.
   */
  Node getSymbolInternal(Kind k, TypeNode tn, const std::string& name);
  /**
   * Get character vector, add internal vector of characters for c.
   */
  void getCharVectorInternal(Node c, std::vector<Node>& chars);
  /** Is k a kind that is printed as an indexed operator in LFSC? */
  static bool isIndexedOperatorKind(Kind k);
  /** get indices for printing the operator of n in the LFSC format */
  static std::vector<Node> getOperatorIndices(Kind k, Node n);
  /** terms with different syntax than smt2 */
  std::map<std::tuple<Kind, TypeNode, std::string>, Node> d_symbolsMap;
  /** the set of all internally generated symbols */
  std::unordered_set<Node> d_symbols;
  /** symbols to builtin kinds*/
  std::map<Node, Kind> d_symbolToBuiltinKind;
  /** arrow type constructor */
  TypeNode d_arrow;
  /** the type of LFSC sorts, which can appear in terms */
  TypeNode d_sortType;
  /** Used for getting unique index for variable */
  std::map<Node, size_t> d_varIndex;
  /** Cache for typeAsNode */
  std::map<TypeNode, Node> d_typeAsNode;
  /** Used for interpreted builtin parametric sorts */
  std::map<Kind, Node> d_typeKindToNodeCons;
};

}  // namespace proof
}  // namespace cvc5

#endif
