/*********************                                                        */
/*! \file theory_bags_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory rewriter.
 **/

#include "theory/bags/theory_bags_rewriter.h"

#include "normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

RewriteResponse TheoryBagsRewriter::postRewrite(TNode n)
{
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    return RewriteResponse(REWRITE_DONE, n);
  }
  // n is not in a normal form
  if (NormalForm::AreChildrenInNormalForm(n))
  {
    // rewrite n to be in a normal form
    Node normal = NormalForm::getNormalForm(n);
    return RewriteResponse(REWRITE_AGAIN, normal);
  }
  // children are not in a normal form
  Kind k = n.getKind();
  switch (k)
  {
    case kind::MK_BAG:
    {
      // return emptybag for negative or zero multiplicity
      if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
      {
        // (mkBag x -1) = emptybag
        NodeManager* nm = NodeManager::currentNM();
        Node emptybag = nm->mkConst(EmptyBag(n.getType()));
        return RewriteResponse(REWRITE_AGAIN, emptybag);
      }
      return RewriteResponse(REWRITE_DONE, n);
    }
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheoryBagsRewriter::preRewrite(TNode node)
{
  // TODO(projects#225): complete the code here
  return RewriteResponse(REWRITE_DONE, node);
}
}  // namespace bags
}  // namespace theory
}  // namespace CVC4
