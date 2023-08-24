/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ceg_dt_instantiator.
 */

#include "theory/quantifiers/cegqi/ceg_dt_instantiator.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void DtInstantiator::reset(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort)
{
}

bool DtInstantiator::hasProcessEqualTerm(CegInstantiator* ci,
                                         SolvedForm& sf,
                                         Node pv,
                                         CegInstEffort effort)
{
  return true;
}

bool DtInstantiator::processEqualTerms(CegInstantiator* ci,
                                       SolvedForm& sf,
                                       Node pv,
                                       std::vector<Node>& eqc,
                                       CegInstEffort effort)
{
  Trace("cegqi-dt-debug") << "try based on constructors in equivalence class."
                          << std::endl;
  // look in equivalence class for a constructor
  for (unsigned k = 0, size = eqc.size(); k < size; k++)
  {
    Node n = eqc[k];
    if (n.getKind() == APPLY_CONSTRUCTOR)
    {
      Trace("cegqi-dt-debug")
          << "...try based on constructor term " << n << std::endl;
      std::vector<Node> children;
      children.push_back(n.getOperator());
      const DType& dt = d_type.getDType();
      unsigned cindex = datatypes::utils::indexOf(n.getOperator());
      // now must solve for selectors applied to pv
      Node val = datatypes::utils::getInstCons(
          pv, dt, cindex, options().datatypes.dtSharedSelectors);
      for (const Node& c : val)
      {
        ci->pushStackVariable(c);
      }
      TermProperties pv_prop_dt;
      if (ci->constructInstantiationInc(pv, val, pv_prop_dt, sf))
      {
        return true;
      }
      // cleanup
      for (unsigned j = 0, nargs = dt[cindex].getNumArgs(); j < nargs; j++)
      {
        ci->popStackVariable();
      }
      break;
    }
  }
  return false;
}

bool DtInstantiator::hasProcessEquality(CegInstantiator* ci,
                                        SolvedForm& sf,
                                        Node pv,
                                        CegInstEffort effort)
{
  return true;
}

bool DtInstantiator::processEquality(CegInstantiator* ci,
                                     SolvedForm& sf,
                                     Node pv,
                                     std::vector<TermProperties>& term_props,
                                     std::vector<Node>& terms,
                                     CegInstEffort effort)
{
  Node val = solve_dt(pv, terms[0], terms[1], terms[0], terms[1]);
  if (!val.isNull())
  {
    TermProperties pv_prop;
    if (ci->constructInstantiationInc(pv, val, pv_prop, sf))
    {
      return true;
    }
  }
  return false;
}

Node DtInstantiator::solve_dt(Node v, Node a, Node b, Node sa, Node sb)
{
  Trace("cegqi-arith-debug2") << "Solve dt : " << v << " " << a << " " << b
                              << " " << sa << " " << sb << std::endl;
  Node ret;
  if (!a.isNull() && a == v)
  {
    ret = sb;
  }
  else if (!b.isNull() && b == v)
  {
    ret = sa;
  }
  else if (!a.isNull() && a.getKind() == APPLY_CONSTRUCTOR)
  {
    if (!b.isNull() && b.getKind() == APPLY_CONSTRUCTOR)
    {
      if (a.getOperator() == b.getOperator())
      {
        for (unsigned i = 0, nchild = a.getNumChildren(); i < nchild; i++)
        {
          Node s = solve_dt(v, a[i], b[i], sa[i], sb[i]);
          if (!s.isNull())
          {
            return s;
          }
        }
      }
    }
    else
    {
      unsigned cindex = DType::indexOf(a.getOperator());
      TypeNode tn = a.getType();
      const DType& dt = tn.getDType();
      Node val = datatypes::utils::getInstCons(
          sb, dt, cindex, options().datatypes.dtSharedSelectors);
      for (size_t i = 0, nchild = val.getNumChildren(); i < nchild; i++)
      {
        Node s = solve_dt(v, a[i], Node::null(), sa[i], val[i]);
        if (!s.isNull())
        {
          return s;
        }
      }
    }
  }
  else if (!b.isNull() && b.getKind() == APPLY_CONSTRUCTOR)
  {
    // flip sides
    return solve_dt(v, b, a, sb, sa);
  }
  if (!ret.isNull())
  {
    // ensure does not contain v
    if (expr::hasSubterm(ret, v))
    {
      ret = Node::null();
    }
  }
  return ret;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
