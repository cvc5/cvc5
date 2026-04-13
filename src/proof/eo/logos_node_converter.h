/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Logos node conversion
 */
#include "cvc5_private.h"

#ifndef CVC5__PROOF__EO__LOGOS_NODE_CONVERTER_H
#define CVC5__PROOF__EO__LOGOS_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "proof/eo/eo_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * This is a helper class for the Eunoia printer that prints a proof in the
 * format expected by the Logos checker.
 * 
 * An example of such a proof is:
 * 
 * import Cpc.Logos
 * open Eo
 * def t1 : Term := (Term.UConst 1 Term.Int)
 * def t2 : Term := (Term.UConst 2 Term.Int)
 * def t3 : Term := (Term.Apply Term.eq t2)
 * def t4 : Term := (Term.Apply t3 t1)
 * def t5 : Term := (Term.Apply Term.eq t1)
 * def t6 : Term := (Term.Apply t5 t2)
 * def t7 : Term := (Term.Apply Term.not t6)
 * def s0 : CState := logos_init_state
 * def s1 : CState := (logos_invoke_assume s0 t4)
 * def s2 : CState := (logos_invoke_assume s1 t7)
 * def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.symm CArgList.nil
 *                    (CIndexList.cons 0 CIndexList.nil)))
 * def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.contra CArgList.nil
 *                    (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
 * #eval! (logos_state_is_refutation s4)
 * 
 * This node converter involves rewriting cvc5 terms to their corresponding
 * deep embedding syntax in the Lean signature.
 */
class LogosNodeConverter : public EoNodeConverter
{
 public:
  LogosNodeConverter(NodeManager* nm);
  ~LogosNodeConverter();

  /** Convert at post-order traversal */
  Node postConvert(Node n) override;
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /**
   * Type as node, returns a node that prints in the form that ALF will
   * interpret as the type tni. This method is required since types can be
   * passed as arguments to terms and proof rules.
   */
  Node typeAsNode(TypeNode tni) override;
  /** Replace all string utility, replaces all occurrences of from by to in str. */
static std::string replace_all(std::string str,
                        const std::string& from,
                        const std::string& to);
 private:
  /** Returns the Lean identifier for an SMT-LIB identifier. */
  std::string cleanSmtId(const std::string& str);
  /** The number of uninterpreted constants we have allocated */
  size_t d_constIdCount;
  /** Cache for typeAsNode */
  std::map<TypeNode, Node> d_ltypeAsNode;
  /** The number of uninterpreted sorts we have allocated */
  size_t d_sortIdCount;
  /** type as node datatype */
  Node typeAsNodeDatatype(const DType& dt, std::unordered_set<TypeNode>& scope);
  /** make list */
  Node mkLogosList(const std::vector<Node>& args, const TypeNode& tn);
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
