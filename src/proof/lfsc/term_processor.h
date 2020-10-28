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

#ifndef CVC4__PROOF__LFSC__TERM_PROCESSOR_H
#define CVC4__PROOF__LFSC__TERM_PROCESSOR_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace proof {
  
class TermProcessCallback
{
public:
  TermProcessCallback(){}
  virtual ~TermProcessCallback(){}
  Node convert(Node n, bool toInternal);
  virtual Node convertInternal(Node n) = 0;
  virtual Node convertExternal(Node n) = 0;
  TypeNode convertType(TypeNode n, bool toInternal);
  virtual TypeNode convertInternalType(TypeNode n) = 0;
  virtual TypeNode convertExternalType(TypeNode n) = 0;
};

class TermProcessor
{
 public:
   TermProcessor(TermProcessCallback * cb);
   ~TermProcessor(){}
  /** convert to internal
   *
   * This converts the node n to the internal shape that it would be in
   * LFSC printer. This means that n-ary applications are converted
   * to (left-associative) chains.
   */
  Node toInternal(Node n);
  /** convert to external
   *
   * Inverse of the above translation
   */
  Node toExternal(Node n);

  /** convert to internal
   *
   * This converts the type node tn to the internal shape that it would be in
   * LFSC printer. This means that n-ary applications (e.g. of function type)
   * are converted to (left-associative) chains.
   */
  TypeNode toInternalType(TypeNode tn);
  /** convert to external
   *
   * Inverse of the above translation
   */
  TypeNode toExternalType(TypeNode tn);

 private:
  /** convert */
  Node convert(Node n, bool toInternal);
  /** convert */
  TypeNode convertType(TypeNode tn, bool toInternal);
  /** The callback */
  TermProcessCallback * d_cb;
  /** Node caches */
  std::unordered_map<Node, Node, NodeHashFunction> d_cache[2];
  /** TypeNode caches */
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction> d_tcache[2];
};

}  // namespace proof
}  // namespace CVC4

#endif
