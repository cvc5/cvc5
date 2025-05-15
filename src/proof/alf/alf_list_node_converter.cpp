/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion for list variables in DSL rules
 */

#include "proof/alf/alf_list_node_converter.h"

#include "expr/emptyset.h"
#include "expr/nary_term_util.h"
#include "expr/sequence.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/strings/word.h"

namespace cvc5::internal {
namespace proof {

AlfListNodeConverter::AlfListNodeConverter(NodeManager* nm,
                                           BaseAlfNodeConverter& tproc,
                                           const std::map<Node, Node>& adtcMap,
                                           bool useSingletonElim)
    : NodeConverter(nm),
      d_tproc(tproc),
      d_useSingletonElim(useSingletonElim),
      d_adtcMap(adtcMap)
{
}

Node AlfListNodeConverter::preConvert(Node n)
{
  Kind k = n.getKind();
  if (k == Kind::SET_EMPTY_OF_TYPE || k == Kind::SEQ_EMPTY_OF_TYPE)
  {
    if (n[0].getKind() == Kind::TYPE_OF)
    {
      Node t = n[0][0];
      std::map<Node, Node>::const_iterator it = d_adtcMap.find(t);
      if (it != d_adtcMap.end())
      {
        std::stringstream ss;
        ss << it->second[0];
        TypeNode tn = d_nm->mkSort(ss.str());
        if (k == Kind::SET_EMPTY_OF_TYPE)
        {
          tn = d_nm->mkSetType(tn);
          return d_tproc.convert(d_nm->mkConst(EmptySet(tn)));
        }
        else
        {
          tn = d_nm->mkSequenceType(tn);
          Node ntn = d_tproc.typeAsNode(tn);
          // must use $seq_empty side condition, since string and sequence
          // have different representations in the Eunoia signature
          return d_tproc.mkInternalApp("$seq_empty", {ntn}, n.getType());
        }
      }
    }
    Assert(false) << "AlfListNodeConverter: unhandled term " << n;
  }
  else
  {
    Assert(k != Kind::TYPE_OF) << "AlfListNodeConverter: unhandled term " << n;
  }
  return n;
}

Node AlfListNodeConverter::postConvert(Node n)
{
  if (!d_useSingletonElim)
  {
    return n;
  }
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::STRING_CONCAT:
    case Kind::BITVECTOR_ADD:
    case Kind::BITVECTOR_MULT:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR:
    case Kind::BITVECTOR_XOR:
    case Kind::FINITE_FIELD_ADD:
    case Kind::FINITE_FIELD_MULT:
    case Kind::OR:
    case Kind::AND:
    case Kind::SEP_STAR:
    case Kind::ADD:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::BITVECTOR_CONCAT:
    case Kind::REGEXP_CONCAT:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_INTER:
      // operators with a ground null terminator
      break;
    default:
      // not an n-ary kind
      return n;
  }
  size_t nlistChildren = 0;
  for (const Node& nc : n)
  {
    if (!expr::isListVar(nc))
    {
      nlistChildren++;
    }
  }
  // if less than 2 non-list children, it might collapse to a single element
  if (nlistChildren < 2)
  {
    return d_tproc.mkInternalApp("$singleton_elim", {n}, n.getType());
  }
  return n;
}

}  // namespace proof
}  // namespace cvc5::internal
