/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus random enumerator.
 */

#include "theory/quantifiers/sygus/sygus_random_enumerator.h"

#include "expr/dtype_cons.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/rewriter.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void SygusRandomEnumerator::initialize(Node e)
{
  d_tn = e.getType();
  Assert(d_tn.isDatatype());
  Assert(d_tn.getDType().isSygus());
  SygusTypeInfo sti;
  sti.initialize(d_tds, d_tn);
  std::vector<TypeNode> stns;
  sti.getSubfieldTypes(stns);
  // We will be using the datatype constructors a lot, so we cache them here.
  for (const TypeNode& stn : stns)
  {
    for (const std::shared_ptr<DTypeConstructor>& cons :
         stn.getDType().getConstructors())
    {
      if (cons->getNumArgs() == 0)
      {
        d_noArgCons[stn].push_back(cons);
      }
      else
      {
        d_argCons[stn].push_back(cons);
      }
    }
  }
}

bool SygusRandomEnumerator::increment()
{
  Node n, bn;
  do
  {
    // Generate the next sygus term.
    n = incrementH();
    bn = d_tds->sygusToBuiltin(n);
    bn = extendedRewrite(bn);
    // Ensure that the builtin counterpart is unique (up to rewriting).
  } while (d_cache.find(bn) != d_cache.cend());
  d_cache.insert(bn);
  d_currTerm = n;
  return true;
}

Node SygusRandomEnumerator::incrementH()
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Random& rnd = Random::getRandom();
  double p = options().quantifiers.sygusEnumRandomP;

  Node mainSkolem = sm->mkDummySkolem("sygus_rand", d_tn);
  // List of skolems with no corresponding constructor.
  std::vector<Node> remainingSkolems;
  remainingSkolems.push_back(mainSkolem);
  // List of terms with corresponding constructors. We do not immediately
  // construct sygus terms (possibly containing holes) for those skolems.
  // Instead, we wait until we are done picking constructors for all skolems. We
  // do so to immediately construct ground terms for all of them following their
  // order in this stack.
  std::vector<Node> stack;
  // Constructors corresponding to each skolem.
  std::unordered_map<Node, std::shared_ptr<DTypeConstructor>> skolemCons;
  // Ground terms corresponding to each skolem.
  std::unordered_map<Node, Node> groundTerm;
  // Sub-skolems needed for skolems with constructors that take arguments.
  std::unordered_map<Node, std::vector<Node>> subSkolems;

  // We stop when we get a tails or there are no more skolems to process.
  while (rnd.pickWithProb(p) && !remainingSkolems.empty())
  {
    // Pick a random skolem from the remaining ones and remove it from the list.
    size_t r = rnd() % remainingSkolems.size();
    Node currSkolem = remainingSkolems[r];
    remainingSkolems.erase(remainingSkolems.cbegin() + r);
    // Add the picked skolem to stack for later processing.
    TypeNode currSkolemType = currSkolem.getType();
    // If the type current skolem is not a subfield type of `d_tn`, we replace
    // it with a ground value of its type.
    if (d_argCons[currSkolemType].empty()
        && d_noArgCons[currSkolemType].empty())
    {
      groundTerm[currSkolem] = nm->mkGroundValue(currSkolemType);
      continue;
    }
    stack.push_back(currSkolem);
    // Pick a random constructor that takes arguments for this skolem. If there
    // is none, pick a random no-argument constructor.
    skolemCons[currSkolem] =
        d_argCons[currSkolemType].empty()
            ? d_noArgCons[currSkolemType]
                         [rnd() % d_noArgCons[currSkolemType].size()]
            : d_argCons[currSkolemType]
                       [rnd() % d_argCons[currSkolemType].size()];
    // Create a sub-skolem for each constructor argument and add them to the
    // list of remaining skolems.
    for (size_t i = 0, n = skolemCons[currSkolem]->getNumArgs(); i < n; ++i)
    {
      TypeNode subSkolemType = skolemCons[currSkolem]->getArgType(i);
      Node subSkolem = sm->mkDummySkolem("sygus_rand", subSkolemType);
      remainingSkolems.push_back(subSkolem);
      subSkolems[currSkolem].push_back(subSkolem);
    }
  }

  // If we get a tail, we need to pick no-argument constructors for the
  // remaining skolems. If all constructors take arguments, we use the ground
  // value for the skolems' sygus datatype type.
  for (Node skolem : remainingSkolems)
  {
    TypeNode skolemType = skolem.getType();
    if (d_noArgCons[skolemType].empty())
    {
      groundTerm[skolem] = nm->mkGroundValue(skolemType);
    }
    else
    {
      skolemCons[skolem] =
          d_noArgCons[skolemType][rnd() % d_noArgCons[skolemType].size()];
      stack.push_back(skolem);
    }
  }

  // Build up ground values starting from leaf skolems up to the root/main
  // skolem.
  while (!stack.empty())
  {
    Node currSkolem = stack.back();
    stack.pop_back();
    std::vector<Node> args;
    args.push_back(skolemCons[currSkolem]->getConstructor());
    for (Node subSkolem : subSkolems[currSkolem])
    {
      args.push_back(groundTerm[subSkolem]);
    }
    // We may have already generated a sygus term equivalent to the one we are
    // generating now. In that case, pick the smaller term of the two. This
    // operation allows us to generate more refined terms over time.
    groundTerm[currSkolem] = getMin(nm->mkNode(kind::APPLY_CONSTRUCTOR, args));
  }

  return groundTerm[mainSkolem];
}

Node SygusRandomEnumerator::getMin(Node n)
{
  TypeNode tn = n.getType();
  Node bn = d_tds->sygusToBuiltin(n);
  bn = extendedRewrite(bn);
  // Did we calculate the size of `n` before?
  if (d_size.find(n) == d_size.cend())
  {
    // If not, calculate its size and cache it.
    d_size[n] = datatypes::utils::getSygusTermSize(n);
  }
  // Did we come across an equivalent term before? If so, is the equivalent term
  // smaller than `n`?
  if (d_minSygus[tn][bn].isNull() || d_size[n] < d_size[d_minSygus[tn][bn]])
  {
    d_minSygus[tn][bn] = n;
  }
  else
  {
    n = d_minSygus[tn][bn];
  }
  return n;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
