/*********************                                                        */
/*! \file term_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term processing utilities
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

/** 
  * Generic term processor callback. This is a postrewrite callback that
  * converts terms into an "internal" form.
  */
class TermProcessCallback
{
 public:
  TermProcessCallback() {}
  virtual ~TermProcessCallback() {}
  /** Convert to/from internal */
  Node convert(Node n, bool toInternal);
  /** 
   * Convert internal, where n is a term of the form:
   *   (f i_1 ... i_m)
   * where i_1, ..., i_m are "internal" terms. In particular, these terms
   * have been returned by this class on a previous call to convertInternal.
   */
  virtual Node convertInternal(Node n);
  /**
   * Intended to perform the inverse of the above transformation.
   * Convert external, where n is a term of the form:
   *   (f e_1 ... e_m)
   * where e_1, ..., e_m are "external" terms. In particular, these terms
   * have been returned by this class on a previous call to convertExternal.
   *
   * This method is optional.
   */
  virtual Node convertExternal(Node n);
  /** Same as above, for types. */
  TypeNode convertType(TypeNode n, bool toInternal);
  /** Convert type to internal representation */
  virtual TypeNode convertInternalType(TypeNode n);
  /** Convert type to external representation */
  virtual TypeNode convertExternalType(TypeNode n);
};

/**
 * A term processor for terms and types. Implements a term traversal,
 * calling the provided process callback at postrewrite (at post-traversal).
 */
class TermProcessor
{
 public:
  TermProcessor(TermProcessCallback* cb);
  ~TermProcessor() {}
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
  TermProcessCallback* d_cb;
  /** Node caches */
  std::unordered_map<Node, Node, NodeHashFunction> d_cache[2];
  /** TypeNode caches */
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction> d_tcache[2];
};

}  // namespace proof
}  // namespace CVC4

#endif
