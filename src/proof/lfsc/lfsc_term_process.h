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

#ifndef CVC4__PROOF__LFSC__LFSC_TERM_CONVERSION_H
#define CVC4__PROOF__LFSC__LFSC_TERM_CONVERSION_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace proof {

class LfscTermProcess
{
 public:
  /** convert to internal
   *
   * This converts the node n to the internal shape that it would be in
   * LFSC printer. This means that n-ary applications are converted
   * to (left-associative) chains.
   */
  static Node toInternal(Node n);
  /** convert to external
   *
   * Inverse of the above translation
   */
  static Node toExternal(Node n);

  /** convert to internal
   *
   * This converts the type node tn to the internal shape that it would be in
   * LFSC printer. This means that n-ary applications (e.g. of function type)
   * are converted to (left-associative) chains.
   */
  static TypeNode toInternalType(TypeNode tn);
  /** convert to external
   *
   * Inverse of the above translation
   */
  static TypeNode toExternalType(TypeNode tn);

 private:
  /** convert */
  static Node convert(Node n, bool toInternal);
  /** convert to internal */
  static Node computeInternal(Node n);
  /** convert to external */
  static Node computeExternal(Node n);
  /** convert */
  static TypeNode convertType(TypeNode tn, bool toInternal);
  /** convert to internal */
  static TypeNode computeInternalType(TypeNode tn);
  /** convert to external */
  static TypeNode computeExternalType(TypeNode tn);
};

}  // namespace proof
}  // namespace CVC4

#endif
