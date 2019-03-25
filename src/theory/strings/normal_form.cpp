/*********************                                                        */
/*! \file normal_form.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of normal form data structure for the theory of
 **  strings.
 **/

#include "theory/strings/normal_form.h"

#include "options/strings_options.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

void NormalForm::reverse() { 
  std::reverse(d_nf.begin(), d_nf.end()); 
  
}
  
void NormalForm::splitConstant(unsigned index,
                                              Node c1,
                                              Node c2,
                                              bool isRev)
{
  Assert(Rewriter::rewrite(NodeManager::currentNM()->mkNode(
             STRING_CONCAT, isRev ? c2 : c1, isRev ? c1 : c2))
         == d_nf[index]);
  d_nf.insert(d_nf.begin() + index + 1, c2);
  d_nf[index] = c1;
  // update the dependency indices
  // notice this is not critical for soundness: not doing the below incrementing
  // will only lead to overapproximating when antecedants are required in
  // explanations
  for (std::map<Node, std::map<bool, unsigned> >::iterator itnd =
           d_exp_dep.begin();
       itnd != d_exp_dep.end();
       ++itnd)
  {
    for (std::map<bool, unsigned>::iterator itnd2 = itnd->second.begin();
         itnd2 != itnd->second.end();
         ++itnd2)
    {
      // See if this can be incremented: it can if this literal is not relevant
      // to the current index, and hence it is not relevant for both c1 and c2.
      Assert(itnd2->second >= 0 && itnd2->second <= d_nf.size());
      bool increment = (itnd2->first == isRev)
                           ? itnd2->second > index
                           : (d_nf.size() - 1 - itnd2->second) < index;
      if (increment)
      {
        d_exp_dep[itnd->first][itnd2->first] = itnd2->second + 1;
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
  for( unsigned k=0; k<2; k++ ){
    unsigned val = k == 0 ? new_val : new_rev_val;
    std::map<bool, unsigned>::iterator itned = d_exp_dep[exp].find(k == 1);
    if (itned == d_exp_dep[exp].end())
    {
      Trace("strings-process-debug") << "Deps : set dependency on " << exp << " to " << val << " isRev=" << (k==0) << std::endl;
      d_exp_dep[exp][k == 1] = val;
    }else{
      Trace("strings-process-debug") << "Deps : Multiple dependencies on " << exp << " : " << itned->second << " " << val << " isRev=" << (k==0) << std::endl;
      //if we already have a dependency (in the case of non-linear string equalities), it is min/max
      bool cmp = val > itned->second;
      if( cmp==(k==1) ){
        d_exp_dep[exp][k == 1] = val;
      }
    }
  }
}

void NormalForm::getExplanation(int index,
                                               bool isRev,
                                               std::vector<Node>& curr_exp)
{
  if (index == -1 || !options::stringMinPrefixExplain())
  {
    curr_exp.insert(curr_exp.end(), d_exp.begin(), d_exp.end());
    return;
  }
  for (const Node& exp : d_exp)
  {
    int dep = static_cast<int>(d_exp_dep[exp][isRev]);
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

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
