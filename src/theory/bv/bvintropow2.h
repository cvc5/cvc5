/*********************                                                        */
/*! \file bvintropow2.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/



#include "cvc4_private.h"
#include "expr/node.h"

#include <vector>
#include <ext/hash_map>

#ifndef __CVC4__THEORY__BV__BV_INTRO_POW_H
#define __CVC4__THEORY__BV__BV_INTRO_POW_H

namespace CVC4 {
namespace theory {
namespace bv {


class BVIntroducePow2 {
public:
  static void pow2Rewrite(std::vector<Node>& assertionsToPreprocess);

private:
  typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeMap;
  static Node pow2Rewrite(Node assertionsToPreprocess, NodeMap& cache);
}; 



}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */


#endif /* __CVC4__THEORY__BV__BV_INTRO_POW_H */
