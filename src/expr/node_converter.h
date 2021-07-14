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
 * Node converter utility
 */

#include "cvc5_private.h"

#ifndef CVC4__EXPR__NODE_CONVERTER_H
#define CVC4__EXPR__NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {

/**
 * A node converter for terms and types. Implements term/type traversals,
 * calling the provided implementations of conversion methods (pre/postConvert
 * and pre/postConvertType) at pre-traversal and post-traversal.
 *
 * This class can be used as a generic method for converting terms/types, which
 * is orthogonal to methods for traversing nodes.
 */
class NodeConverter
{
 public:
  /**
   * @param forceIdem If true, this assumes that terms returned by postConvert
   * and postConvertType should not be converted again.
   */
  NodeConverter(bool forceIdem = true);
  virtual ~NodeConverter() {}
  /**
   * This converts node n based on the preConvert/postConvert methods that can
   * be overriden by instances of this class.
   */
  Node convert(Node n);

  /**
   * This converts type node n based on the preConvertType/postConvertType
   * methods that can be overriden by instances of this class.
   */
  TypeNode convertType(TypeNode tn);

 protected:
  //------------------------- virtual interface
  /** Should we traverse n? */
  virtual bool shouldTraverse(Node n);
  /**
   * Run the conversion for n during pre-order traversal.
   * Returning null is equivalent to saying the node should not be changed.
   */
  virtual Node preConvert(Node n);
  /**
   * Run the conversion for post-order traversal, where notice n is a term
   * of the form:
   *   (f i_1 ... i_m)
   * where i_1, ..., i_m are terms that have been returned by previous calls
   * to postConvert.
   *
   * Returning null is equivalent to saying the node should not be changed.
   */
  virtual Node postConvert(Node n);
  /**
   * Run the conversion, same as `preConvert`, but for type nodes, which notice
   * can be built from children similar to Node.
   */
  virtual TypeNode preConvertType(TypeNode n);
  /**
   * Run the conversion, same as `postConvert`, but for type nodes, which notice
   * can be built from children similar to Node.
   */
  virtual TypeNode postConvertType(TypeNode n);
  //------------------------- end virtual interface
 private:
  /** Add to cache */
  void addToCache(TNode cur, TNode ret);
  /** Add to type cache */
  void addToTypeCache(TypeNode cur, TypeNode ret);
  /** Node cache for preConvert */
  std::unordered_map<Node, Node> d_preCache;
  /** Node cache for postConvert */
  std::unordered_map<Node, Node> d_cache;
  /** TypeNode cache for preConvert */
  std::unordered_map<TypeNode, TypeNode> d_preTCache;
  /** TypeNode cache for postConvert */
  std::unordered_map<TypeNode, TypeNode> d_tcache;
  /** Whether this node converter is idempotent. */
  bool d_forceIdem;
};

}  // namespace cvc5

#endif
