/*********************                                                        */
/*! \file instantiation_list.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief list of instantiations
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H
#define CVC4__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace CVC4 {

/** A list of instantiations for a quantified formula */
struct InstantiationList 
{
  InstantiationList(Node q, const std::vector< std::vector<Node> >& inst) : d_quant(q), d_inst(inst){}
  /** The quantified formula */
  Node d_quant;
  /** The instantiation list */
  std::vector< std::vector<Node> > d_inst;
};

/** Print the unsat core to stream out */
std::ostream& operator<<(std::ostream& out, const InstantiationList& ilist);

} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H */
