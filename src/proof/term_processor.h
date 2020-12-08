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
 ** \brief Term processor utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__TERM_PROCESSOR_H
#define CVC4__PROOF__TERM_PROCESSOR_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace proof {

/**
 * A term processor for terms and types. Implements term/type traversals,
 * calling the provided implementations of conversion methods (runConvert and
 * runConvertType) at post-traversal.
 *
 * This class can be used as a generic method for converting terms/types.
 */
class TermProcessor
{
 public:
  TermProcessor();
  virtual ~TermProcessor() {}
  /**
   * This converts node n based on the runConvert method that can be overriden
   * by instances of this class.
   */
  Node convert(Node n);

  /**
   * This converts type node n based on the runConvertType method that can be
   * overriden by instances of this class.
   */
  TypeNode convertType(TypeNode tn);

 protected:
  //------------------------- virtual interface
  /** Should we traverse n? */
  virtual bool shouldTraverse(Node n);
  /**
   * Run the conversion, where n is a term of the form:
   *   (f i_1 ... i_m)
   * where i_1, ..., i_m are terms that have been returned by previous calls
   * to runConvert.
   */
  virtual Node runConvert(Node n);
  /**
   * Run the conversion, same as above, but for type nodes, which notice can
   * be built from children similar to Node.
   */
  virtual TypeNode runConvertType(TypeNode n);
  //------------------------- end virtual interface
 private:
  /** convert */
  Node convertInternal(Node n);
  /** convert */
  TypeNode convertTypeInternal(TypeNode tn);
  /** Node caches */
  std::unordered_map<Node, Node, NodeHashFunction> d_cache;
  /** TypeNode caches */
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction> d_tcache;
};

}  // namespace proof
}  // namespace CVC4

#endif
