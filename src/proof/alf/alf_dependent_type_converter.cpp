/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of conversion between approximate and dependent types.
 */

#include "proof/alf/alf_dependent_type_converter.h"

#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {
namespace proof {

AlfDependentTypeConverter::AlfDependentTypeConverter(
    NodeManager* nm, BaseAlfNodeConverter& tproc)
    : d_nm(nm), d_tproc(tproc), d_typeCounter(0), d_intCounter(0)
{
  d_sortType = nm->mkSort("Type");
  d_kindToName[Kind::ARRAY_TYPE] = "Array";
  d_kindToName[Kind::BITVECTOR_TYPE] = "BitVec";
  d_kindToName[Kind::FLOATINGPOINT_TYPE] = "FloatingPoint";
  d_kindToName[Kind::FINITE_FIELD_TYPE] = "FiniteField";
  d_kindToName[Kind::SET_TYPE] = "Set";
  d_kindToName[Kind::BAG_TYPE] = "Bag";
  d_kindToName[Kind::SEQUENCE_TYPE] = "Seq";
}

Node AlfDependentTypeConverter::process(const TypeNode& tn)
{
  // if abstract
  if (tn.isAbstract())
  {
    Kind ak = tn.getAbstractedKind();
    switch (ak)
    {
      case Kind::ABSTRACT_TYPE:
      case Kind::FUNCTION_TYPE:
      case Kind::TUPLE_TYPE:
      {
        // Note that we don't have a way to convert function or tuples here,
        // since they don't have a fixed arity. Hence, they are approximated
        // by a type variable.
        std::stringstream ss;
        ss << "@T" << d_typeCounter;
        d_typeCounter++;
        Node n = d_tproc.mkInternalSymbol(ss.str(), d_sortType);
        d_params.push_back(n);
        return n;
      }
      break;
      case Kind::BITVECTOR_TYPE:
      case Kind::FINITE_FIELD_TYPE:
      case Kind::FLOATINGPOINT_TYPE:
      {
        size_t nindices = (ak == Kind::FLOATINGPOINT_TYPE ? 2 : 1);
        std::vector<Node> indices;
        for (size_t i = 0; i < nindices; i++)
        {
          std::stringstream ss;
          ss << "@n" << d_intCounter;
          d_intCounter++;
          Node n = d_tproc.mkInternalSymbol(ss.str(), d_nm->integerType());
          d_params.push_back(n);
          indices.push_back(n);
        }
        Node ret = d_tproc.mkInternalApp(d_kindToName[ak], indices, d_sortType);
        return ret;
      }
      break;
      default: Unhandled() << "Cannot process abstract type kind " << ak; break;
    }
  }
  if (tn.getNumChildren() == 0)
  {
    std::stringstream ss;
    ss << tn;
    return d_tproc.mkInternalSymbol(ss.str(), d_sortType);
  }
  // get the arguments
  std::vector<Node> asNode;
  for (size_t i = 0, nchild = tn.getNumChildren(); i < nchild; i++)
  {
    Node pt = process(tn[i]);
    asNode.push_back(pt);
  }
  return d_tproc.mkInternalApp(
      d_kindToName[tn.getKind()], {asNode}, d_sortType);
}
const std::vector<Node>& AlfDependentTypeConverter::getFreeParameters() const
{
  return d_params;
}

}  // namespace proof
}  // namespace cvc5::internal
