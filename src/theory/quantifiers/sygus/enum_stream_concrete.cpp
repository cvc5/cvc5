/*********************                                                        */
/*! \file enum_stream_concrete.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for streaming concrete values from enumerated abstract ones
 **/

#include "theory/quantifiers/sygus/enum_stream_concrete.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

namespace StreamPermutation {

StreamPermutation(Node value,
                  const std::map<unsigned, std::vector<Node>>& var_classes)
    : d_tds(tds)
{
  d_value = value;
  for (const std::pair<unsigned, std::vector<Node>>& p : var_classes)
  {
    d_perm_state_class.push_back(PermutationState(p.second));
    d_vars.insert(d_vars.end(), p.second);
  }
}

Node getNextPermutation()
{
  Node perm_value;
  do
  {
    bool new_perm = false;
    std::vector<Node> sub;
    for (unsigned i = 0, size = d_var_classes.size(); i < size; ++i)
    {
      std::vector<Node> perm;
      if (!d_perm_state_class[i].getNextPermutation(perm))
      {
        getLasttPermutation(perm);
      }
      else
      {
        new_perm = true;
      }
      sub.insert(sub.end(), perm.begin(), perm.end());
    }
    // no new permutation
    if (!new_perm)
    {
      return Node::null();
    }
    perm_value = d_value.substitute(
        d_vars.begin(), d_vars.end(), sub.begin(), sub.end());
    perm_value = d_tds->getExtRewriter()->extendedRewrite(perm_value);
    // if permuted value is equivalent modulo rewriting to a previous one, look
    // for another
  } while (!d_perm_values.insert(perm_value).second);
  return perm_value;
}

PermutationState::PermutationState(const std::vector<Node>& vars)
{
  d_vars = vars;
  std::fill(d_seq.begin(), d_seq.end(), 0);
  curr_var_ind = 0;
}

void PermutationState::getLastPermutation(std::vector<Node>& perm)
{
  perm.insert(perm.end(), d_last_perm.begin(), d_last_prem.end());
}

bool PermutationState::getNextPermutation(std::vector<Node>& perm)
{
  // initial case
  if (d_last_perm.empty())
  {
    d_last_perm = vars;
    perm = vars;
    return true;
  }
  // exhausted permutations
  if (d_curr_ind == d_vars.size())
  {
    return false;
  }
  if (d_seq[d_curr_ind] >= d_curr_ind)
  {
    d_seq[d_curr_ind++] = 0;
    return getNextPermutation(perm);
  }
  perm = d_last_perm;
  if (d_curr_ind % 2 == 0)
  {
    // swap with first element
    std::swap(perm[0], perm[d_curr_ind]);
  }
  else
  {
    // swap with element in index in sequence of current index
    std::swap(perm[d_seq[d_curr_ind]], perm[d_curr_ind]);
  }
  d_seq[d_curr_ind] += 1;
  d_curr_ind = 0;
  return true;
}

}

namespace EnumStreamConcrete {
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
