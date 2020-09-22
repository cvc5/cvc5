/*********************                                                        */
/*! \file normal_form.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of normal form data structure for the theory of
 **  strings.
 **/

#include "theory/strings/normal_form.h"

#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

void NormalForm::init(Node base)
{
  Assert(base.getType().isStringLike());
  Assert(base.getKind() != STRING_CONCAT);
  d_base = base;
  d_nf.clear();
  d_isRev = false;
  d_exp.clear();
  d_expDep.clear();

  // add to normal form
  if (!base.isConst() || Word::getLength(base) > 0)
  {
    d_nf.push_back(base);
  }
}

void NormalForm::reverse()
{
  std::reverse(d_nf.begin(), d_nf.end());
  d_isRev = !d_isRev;
}

void NormalForm::splitConstant(unsigned index, Node c1, Node c2)
{
  Assert(Rewriter::rewrite(NodeManager::currentNM()->mkNode(
             STRING_CONCAT, d_isRev ? c2 : c1, d_isRev ? c1 : c2))
         == d_nf[index]);
  d_nf.insert(d_nf.begin() + index + 1, c2);
  d_nf[index] = c1;
  // update the dependency indices
  // notice this is not critical for soundness: not doing the below incrementing
  // will only lead to overapproximating when antecedants are required in
  // explanations
  for (const std::pair<Node, std::map<bool, unsigned> >& pe : d_expDep)
  {
    for (const std::pair<bool, unsigned>& pep : pe.second)
    {
      // See if this can be incremented: it can if this literal is not relevant
      // to the current index, and hence it is not relevant for both c1 and c2.
      Assert(pep.second >= 0 && pep.second <= d_nf.size());
      bool increment = (pep.first == d_isRev)
                           ? pep.second > index
                           : (d_nf.size() - 1 - pep.second) < index;
      if (increment)
      {
        d_expDep[pe.first][pep.first] = pep.second + 1;
      }
    }
  }
}

void NormalForm::addToExplanation(Node exp,
                                  unsigned new_val,
                                  unsigned new_rev_val)
{
  if (std::find(d_exp.begin(), d_exp.end(), exp) == d_exp.end())
  {
    d_exp.push_back(exp);
  }
  for (unsigned k = 0; k < 2; k++)
  {
    unsigned val = k == 0 ? new_val : new_rev_val;
    std::map<bool, unsigned>::iterator itned = d_expDep[exp].find(k == 1);
    if (itned == d_expDep[exp].end())
    {
      Trace("strings-process-debug")
          << "Deps : set dependency on " << exp << " to " << val
          << " isRev=" << (k == 0) << std::endl;
      d_expDep[exp][k == 1] = val;
    }
    else
    {
      Trace("strings-process-debug")
          << "Deps : Multiple dependencies on " << exp << " : " << itned->second
          << " " << val << " isRev=" << (k == 0) << std::endl;
      // if we already have a dependency (in the case of non-linear string
      // equalities), it is min/max
      bool cmp = val > itned->second;
      if (cmp == (k == 1))
      {
        d_expDep[exp][k == 1] = val;
      }
    }
  }
}

void NormalForm::getExplanation(int index, std::vector<Node>& curr_exp)
{
  if (index == -1 || !options::stringMinPrefixExplain())
  {
    curr_exp.insert(curr_exp.end(), d_exp.begin(), d_exp.end());
    return;
  }
  for (const Node& exp : d_exp)
  {
    int dep = static_cast<int>(d_expDep[exp][d_isRev]);
    if (dep <= index)
    {
      curr_exp.push_back(exp);
      Trace("strings-explain-prefix-debug") << "  include : ";
    }
    else
    {
      Trace("strings-explain-prefix-debug") << "  exclude : ";
    }
    Trace("strings-explain-prefix-debug") << exp << std::endl;
  }
}

Node NormalForm::collectConstantStringAt(size_t& index)
{
  std::vector<Node> c;
  while (d_nf.size() > index && d_nf[index].isConst())
  {
    c.push_back(d_nf[index]);
    index++;
  }
  if (!c.empty())
  {
    if (d_isRev)
    {
      std::reverse(c.begin(), c.end());
    }
    Node cc = Rewriter::rewrite(utils::mkConcat(c, c[0].getType()));
    Assert(cc.isConst());
    return cc;
  }
  else
  {
    return Node::null();
  }
}

void NormalForm::getExplanationForPrefixEq(NormalForm& nfi,
                                           NormalForm& nfj,
                                           int index_i,
                                           int index_j,
                                           std::vector<Node>& curr_exp)
{
  Assert(nfi.d_isRev == nfj.d_isRev);
  Trace("strings-explain-prefix")
      << "Get explanation for prefix " << index_i << ", " << index_j
      << ", reverse = " << nfi.d_isRev << std::endl;
  // get explanations
  nfi.getExplanation(index_i, curr_exp);
  nfj.getExplanation(index_j, curr_exp);
  Trace("strings-explain-prefix")
      << "Included " << curr_exp.size() << " / "
      << (nfi.d_exp.size() + nfj.d_exp.size()) << std::endl;
  if (nfi.d_base != nfj.d_base)
  {
    Node eq = nfi.d_base.eqNode(nfj.d_base);
    curr_exp.push_back(eq);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
