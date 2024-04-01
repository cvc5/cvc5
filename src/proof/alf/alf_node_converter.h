/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF__ALF_NODE_CONVERTER_H
#define CVC4__PROOF__ALF__ALF_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/skolem_manager.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace proof {

/**
 * Base class for node converters used in the ALF printer. Extends node
 * conversion with a typeAsNode routine.
 */
class BaseAlfNodeConverter : public NodeConverter
{
 public:
  /**
   * Returns the operator of node n.
   * @param n The term whose operator we wish to retrieve.
   * @param reqCast Will the operator be printed in a context where it needs
   * disambiguation (alf.as)? This makes a difference e.g. for symbols with
   * overloading.
   * @return the operator.
   */
  virtual Node getOperatorOfTerm(Node n, bool reqCast = false) = 0;
  /**
   * Type as node, returns a node that prints in the form that ALF will
   * interpret as the type tni. This method is required since types can be
   * passed as arguments to terms and proof rules.
   */
  virtual Node typeAsNode(TypeNode tni) = 0;
};

/**
 * This is a helper class for the ALF printer that converts nodes into
 * form that ALF expects. It should only be used by the ALF printer.
 */
class AlfNodeConverter : public BaseAlfNodeConverter
{
 public:
  AlfNodeConverter();
  ~AlfNodeConverter() {}
  /** Convert at pre-order traversal */
  Node preConvert(Node n) override;
  /** Convert at post-order traversal */
  Node postConvert(Node n) override;
  /**
   * Return the properly named operator for n of the form (f t1 ... tn), where
   * f could be interpreted or uninterpreted.
   * @param n The term whose operator we wish to retrieve.
   * @param reqCast Will the operator be printed in a context where it needs
   * disambiguation (alf.as)? This makes a difference e.g. for symbols with
   * overloading.
   * @return the operator.
   */
  Node getOperatorOfTerm(Node n, bool reqCast = false) override;
  /**
   * Get the null terminator for kind k and type tn. The type tn can be
   * omitted if applications of kind k do not have parametric type.
   *
   * The returned null terminator is *not* converted to internal form.
   *
   * For examples of null terminators, see nary_term_utils.h.
   */
  Node getNullTerminator(Kind k, TypeNode tn);
  /** Make generic list */
  Node mkList(const std::vector<Node>& args);
  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalSymbol(const std::string& name,
                        TypeNode tn,
                        bool useRawSym = true);
  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalApp(const std::string& name,
                     const std::vector<Node>& args,
                     TypeNode ret,
                     bool useRawSym = true);
  /**
   * Type as node, returns a node that prints in the form that ALF will
   * interpret as the type tni. This method is required since types can be
   * passed as arguments to terms and proof rules.
   */
  Node typeAsNode(TypeNode tni) override;
  /**
   * Number of children for closure that we should process. In particular,
   * we ignore patterns for FORALL, so this method returns 2, indicating we
   * should ignore the 3rd child of a FORALL if it exists. It returns 3 for
   * SET_COMPREHENSION, and 2 otherwise.
   */
  size_t getNumChildrenToProcessForClosure(Kind k) const;

 private:
  /** Make alf.nil for the given type. */
  Node mkNil(TypeNode tn);
  /**
   * Get the variable index for free variable fv, or assign a fresh index if it
   * is not yet assigned.
   */
  size_t getOrAssignIndexForConst(Node c);
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /**
   * Make skolem function, if k was constructed by a skolem function identifier
   * (in SkolemManager::mkSkolemFunction) that is supported in the ALF
   * signature.
   */
  Node maybeMkSkolemFun(Node k);
  /** Is k a kind that is printed as an indexed operator in ALF? */
  static bool isIndexedOperatorKind(Kind k);
  /** Do we handle the given skolem id? */
  static bool isHandledSkolemId(SkolemId id);
  /** Get indices for printing the operator of n in the ALF format */
  static std::vector<Node> getOperatorIndices(Kind k, Node n);
  /** The set of all internally generated symbols */
  std::unordered_set<Node> d_symbols;
  /** The type of ALF sorts, which can appear in terms */
  TypeNode d_sortType;
  /** Used for getting unique index for uncategorized skolems */
  std::map<Node, size_t> d_constIndex;
  /** Used for getting unique names for bound variables */
  std::map<std::string, size_t> d_varIndex;
  /** Cache for typeAsNode */
  std::map<TypeNode, Node> d_typeAsNode;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
