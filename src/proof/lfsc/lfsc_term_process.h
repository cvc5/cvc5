/*********************                                                        */
/*! \file lfsc_term_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_TERM_PROCESS_H
#define CVC4__PROOF__LFSC__LFSC_TERM_PROCESS_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"
#include "proof/term_processor.h"

namespace cvc5 {
namespace proof {

class LfscTermProcessor : public TermProcessor
{
 public:
  LfscTermProcessor();
  ~LfscTermProcessor() {}
  /** convert to internal */
  Node runConvert(Node n) override;
  /** convert to internal */
  TypeNode runConvertType(TypeNode tn) override;
  /**
   * Get the null terminator for kind k
   */
  static Node getNullTerminator(Kind k);
  /**
   * Return the properly named operator for n of the form (f t1 ... tn), where
   * f could be interpreted or uninterpreted.  This method is used for cases
   * where it is important to get the term corresponding to the operator for
   * a term. An example is for the base REFL step of nested CONG.
   */
  Node getOperatorOfTerm(Node n, bool macroApply = false);
  /** get or assign variable index for variable v */
  size_t getOrAssignIndexForVar(Node v);
  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalSymbol(const std::string& name, TypeNode tn);

 private:
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /** Type as node */
  Node typeAsNode(TypeNode tni) const;
  /** Get symbol for term */
  Node getSymbolInternalFor(Node n, const std::string& name);
  /** Get symbol internal, (k,tn,name) are for caching, name is the name */
  Node getSymbolInternal(Kind k, TypeNode tn, const std::string& name);
  /**
   * Get character vector, add internal vector of characters for c.
   */
  void getCharVectorInternal(Node c, std::vector<Node>& chars);
  /** terms with different syntax than smt2 */
  std::map<std::tuple<Kind, TypeNode, std::string>, Node> d_symbolsMap;
  /** the set of all internally generated symbols */
  std::unordered_set<Node, NodeHashFunction> d_symbols;
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
