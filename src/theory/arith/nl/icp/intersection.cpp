/*********************                                                        */
/*! \file intersection.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **/

#include "theory/arith/nl/icp/intersection.h"

#ifdef CVC4_POLY_IMP

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "theory/arith/nl/poly_conversion.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

PropagationResult intersect_interval_with(poly::Interval& cur,
                                          const poly::Interval& res,
                                          std::size_t size_threshold)
{
  Trace("nl-icp") << cur << " := " << cur << " intersected with " << res
                  << std::endl;

  if (bitsize(get_lower(res)) > size_threshold
      || bitsize(get_upper(res)) > size_threshold)
  {
    Trace("nl-icp") << "Reached bitsize threshold" << std::endl;
    return PropagationResult::NOT_CHANGED;
  }

  // Basic idea to organize this function:
  // The bounds for res have 5 positions:
  // 1 < 2 (lower(cur)) < 3 < 4 (upper(cur)) < 5

  if (get_upper(res) < get_lower(cur))
  {
    // upper(res) at 1
    Trace("nl-icp") << "res < cur -> conflict" << std::endl;
    return PropagationResult::CONFLICT;
  }
  if (get_upper(res) == get_lower(cur))
  {
    // upper(res) at 2
    if (get_upper_open(res) || get_lower_open(cur))
    {
      Trace("nl-icp") << "meet at lower, but one is open -> conflict"
                      << std::endl;
      return PropagationResult::CONFLICT;
    }
    if (!is_point(cur))
    {
      Trace("nl-icp") << "contracts to point interval at lower" << std::endl;
      cur = poly::Interval(get_upper(res));
      return PropagationResult::CONTRACTED;
    }
    return PropagationResult::NOT_CHANGED;
  }
  Assert(get_upper(res) > get_lower(cur))
      << "Comparison operator does weird stuff.";
  if (get_upper(res) < get_upper(cur))
  {
    // upper(res) at 3
    if (get_lower(res) < get_lower(cur))
    {
      // lower(res) at 1
      Trace("nl-icp") << "lower(cur) .. upper(res)" << std::endl;
      cur.set_upper(get_upper(res), get_upper_open(res));
      return PropagationResult::CONTRACTED;
    }
    if (get_lower(res) == get_lower(cur))
    {
      // lower(res) at 2
      Trace("nl-icp") << "meet at lower, lower(cur) .. upper(res)" << std::endl;
      cur = poly::Interval(get_lower(cur),
                           get_lower_open(cur) || get_lower_open(res),
                           get_upper(res),
                           get_upper_open(res));
      if (get_lower_open(cur) && !get_lower_open(res))
      {
        return PropagationResult::CONTRACTED;
      }
      else
      {
        return PropagationResult::CONTRACTED_WITHOUT_CURRENT;
      }
    }
    Assert(get_lower(res) > get_lower(cur))
        << "Comparison operator does weird stuff.";
    // lower(res) at 3
    Trace("nl-icp") << "cur covers res" << std::endl;
    cur = res;
    return PropagationResult::CONTRACTED_WITHOUT_CURRENT;
  }
  if (get_upper(res) == get_upper(cur))
  {
    // upper(res) at 4
    if (get_lower(res) < get_lower(cur))
    {
      // lower(res) at 1
      Trace("nl-icp") << "res covers cur but meet at upper" << std::endl;
      if (get_upper_open(res) && !get_upper_open(cur))
      {
        cur.set_upper(get_upper(cur), true);
        return PropagationResult::CONTRACTED;
      }
      return PropagationResult::NOT_CHANGED;
    }
    if (get_lower(res) == get_lower(cur))
    {
      // lower(res) at 2
      Trace("nl-icp") << "same bounds but check openness" << std::endl;
      bool changed = false;
      if (get_lower_open(res) && !get_lower_open(cur))
      {
        changed = true;
        cur.set_lower(get_lower(cur), true);
      }
      if (get_upper_open(res) && !get_upper_open(cur))
      {
        changed = true;
        cur.set_upper(get_upper(cur), true);
      }
      if (changed)
      {
        if ((get_lower_open(res) || !get_upper_open(cur))
            && (get_upper_open(res) || !get_upper_open(cur)))
        {
          return PropagationResult::CONTRACTED_WITHOUT_CURRENT;
        }
        else
        {
          return PropagationResult::CONTRACTED;
        }
      }
      return PropagationResult::NOT_CHANGED;
    }
    Assert(get_lower(res) > get_lower(cur))
        << "Comparison operator does weird stuff.";
    // lower(res) at 3
    Trace("nl-icp") << "cur covers res but meet at upper" << std::endl;
    cur = poly::Interval(get_lower(res),
                         get_lower_open(res),
                         get_upper(res),
                         get_upper_open(cur) || get_upper_open(res));
    if (get_upper_open(cur) && !get_upper_open(res))
    {
      return PropagationResult::CONTRACTED;
    }
    else
    {
      return PropagationResult::CONTRACTED_WITHOUT_CURRENT;
    }
  }

  Assert(get_upper(res) > get_upper(cur))
      << "Comparison operator does weird stuff.";
  // upper(res) at 5

  if (get_lower(res) < get_lower(cur))
  {
    // lower(res) at 1
    Trace("nl-icp") << "res covers cur" << std::endl;
    return PropagationResult::NOT_CHANGED;
  }
  if (get_lower(res) == get_lower(cur))
  {
    // lower(res) at 2
    Trace("nl-icp") << "res covers cur but meet at lower" << std::endl;
    if (get_lower_open(res) && is_point(cur))
    {
      return PropagationResult::CONFLICT;
    }
    else if (get_lower_open(res) && !get_lower_open(cur))
    {
      cur.set_lower(get_lower(cur), true);
      return PropagationResult::CONTRACTED;
    }
    return PropagationResult::NOT_CHANGED;
  }
  Assert(get_lower(res) > get_lower(cur))
      << "Comparison operator does weird stuff.";
  if (get_lower(res) < get_upper(cur))
  {
    // lower(res) at 3
    Trace("nl-icp") << "lower(res) .. upper(cur)" << std::endl;
    cur.set_lower(get_lower(res), get_lower_open(res));
    return PropagationResult::CONTRACTED;
  }
  if (get_lower(res) == get_upper(cur))
  {
    // lower(res) at 4
    if (get_lower_open(res) || get_upper_open(cur))
    {
      Trace("nl-icp") << "meet at upper, but one is open -> conflict"
                      << std::endl;
      return PropagationResult::CONFLICT;
    }
    if (!is_point(cur))
    {
      Trace("nl-icp") << "contracts to point interval at upper" << std::endl;
      cur = poly::Interval(get_lower(res));
      return PropagationResult::CONTRACTED;
    }
    return PropagationResult::NOT_CHANGED;
  }

  Assert(get_lower(res) > get_upper(cur));
  // lower(res) at 5
  Trace("nl-icp") << "res > cur -> conflict" << std::endl;
  return PropagationResult::CONFLICT;
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
