/*********************                                                        */
/*! \file let_binding.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A let binding
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LET_BINDING_H
#define CVC4__PROOF__LFSC__LET_BINDING_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "context/cdhashmap.h"
#include "context/cdlist.h"

namespace CVC4 {
namespace proof {

/**
 * A let binding is a list and a map that can be printed as a let expression.
 * In particular, the list d_letList is ordered such that
 * d_letList[i] does not contain subterm d_letList[j] for j>i.
 * It is intended that d_letList contains only unique nodes. Each node
 * in d_letList is mapped to a unique identifier in d_letMap.
 *
 * If a term is mapped to identifier 0, then it is not letified. This is
 * used to disable letification for certain terms.
 */
class LetBinding
{
  typedef context::CDList<Node> NodeList;
  typedef context::
      CDHashMap<Node, uint32_t, NodeHashFunction>
          NodeIdMap;
public:
  LetBinding();
  /** */
  void push(Node n);
  /** */
  void pop();
  /** */
  uint32_t getId(Node n) const;
  /** convert */
  //Node convert(Node n) const;
private:
  /** An internal context */
  context::Context d_context;
  /** Visit list */
  NodeList d_visitList;
  /** Count */
  NodeIdMap d_count;
  /** The let list */
  NodeList d_letList;
  /** The let map */
  NodeIdMap d_letMap;
};

}  // namespace proof
}  // namespace CVC4

#endif
