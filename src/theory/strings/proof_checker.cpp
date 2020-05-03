/*********************                                                        */
/*! \file proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of strings proof
 **/

#include "theory/strings/proof_checker.h"

#include "theory/rewriter.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/term_registry.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node StringProofRuleChecker::checkInternal(PfRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args)
{
  if (id == PfRule::CONCAT_EQ)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    Node eqs = children[0];
    if (eqs.getKind() != EQUAL)
    {
      return Node::null();
    }
    // convert to concatenation form
    std::vector<Node> svec;
    std::vector<Node> tvec;
    utils::getConcat(eqs[0], svec);
    utils::getConcat(eqs[1], tvec);
    // extract the Boolean corresponding to whether the rule is reversed
    bool isRev;
    if (!getBool(args[0], isRev))
    {
      return Node::null();
    }
    size_t index = 0;
    size_t nchilds = svec.size();
    size_t nchildt = tvec.size();
    std::vector<Node> sremVec;
    std::vector<Node> tremVec;
    // scan the concatenation until we exhaust child proofs
    while (index < nchilds && index < nchildt)
    {
      Node currS = svec[isRev ? (nchilds - 1 - index) : index];
      Node currT = tvec[isRev ? (nchildt - 1 - index) : index];
      if (currS != currT)
      {
        if (currS.isConst() && currT.isConst())
        {
          size_t sindex;
          // get the equal prefix/suffix, strip and add the remainders
          Node currR = Word::splitConstant(currS, currT, sindex, isRev);
          if (!currR.isNull())
          {
            // add the constant to remainder vec
            std::vector<Node>& rem = sindex == 0 ? sremVec : tremVec;
            rem.push_back(currR);
            // ignore the current component
            index++;
            // In other words, if we have (currS,currT) = ("ab","abc"), then we
            // proceed to the next component and add currR = "c" to tremVec.
          }
          // otherwise if we are not the same prefix, then both will be added
          // Notice that we do not add maximal prefixes, in other words,
          // ("abc", "abd") may be added to the remainder vectors, and not
          // ("c", "d").
        }
        break;
      }
      index++;
    }
    Assert(index <= nchilds);
    Assert(index <= nchildt);
    // the remainders are equal
    sremVec.insert(isRev ? sremVec.begin() : sremVec.end(),
                   svec.begin() + (isRev ? 0 : index),
                   svec.begin() + nchilds - (isRev ? index : 0));
    tremVec.insert(isRev ? tremVec.begin() : tremVec.end(),
                   tvec.begin() + (isRev ? 0 : index),
                   tvec.begin() + nchildt - (isRev ? index : 0));
    // convert back to node
    Node srem = utils::mkConcat(sremVec, eqs[0].getType());
    Node trem = utils::mkConcat(tremVec, eqs[1].getType());
    return srem.eqNode(trem);
  }
  else if (id == PfRule::CONCAT_UNIFY)
  {
    Assert(children.size() == 2);
    Assert(args.size() == 1);
    // extract the Boolean corresponding to whether the rule is reversed
    bool isRev;
    if (!getBool(args[0], isRev))
    {
      return Node::null();
    }
    Node eqs = children[0];
    if (eqs.getKind() != EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> svec;
    std::vector<Node> tvec;
    utils::getConcat(eqs[0], svec);
    utils::getConcat(eqs[1], tvec);
    Node s0 = svec[isRev ? svec.size() - 1 : 0];
    Node t0 = tvec[isRev ? tvec.size() - 1 : 0];
    Node eql = children[1];
    if (eql.getKind() != EQUAL)
    {
      return Node::null();
    }
    Node ls = eql[0];
    Node lt = eql[1];
    if (ls.getKind() != STRING_LENGTH || lt.getKind() != STRING_LENGTH
        || ls[0] != s0 || lt[0] != t0)
    {
      return Node::null();
    }
    return s0.eqNode(t0);
  }
  else if (id == PfRule::CONCAT_CONFLICT)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    // extract the Boolean corresponding to whether the rule is reversed
    bool isRev;
    if (!getBool(args[0], isRev))
    {
      return Node::null();
    }
    Node eqs = children[0];
    if (eqs.getKind() != EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> svec;
    std::vector<Node> tvec;
    utils::getConcat(eqs[0], svec);
    utils::getConcat(eqs[1], tvec);
    Node s0 = svec[isRev ? svec.size() - 1 : 0];
    Node t0 = tvec[isRev ? tvec.size() - 1 : 0];
    if (!s0.isConst() || !t0.isConst())
    {
      // not constants
      return Node::null();
    }
    size_t sindex;
    Node r0 = Word::splitConstant(s0, t0, sindex, isRev);
    if (!r0.isNull())
    {
      // Not a conflict due to constants, i.e. s0 is a prefix of t0 or vice
      // versa.
      return Node::null();
    }
    return NodeManager::currentNM()->mkConst(false);
  }
  else if (id == PfRule::CONCAT_LPROP)
  {
    // TODO
  }
  else if (id == PfRule::CONCAT_CPROP)
  {
    // TODO
  }
  else if (id == PfRule::CTN_NOT_EQUAL)
  {
    // TODO
  }
  else if (id == PfRule::STRINGS_REDUCTION
           || id == PfRule::STRINGS_EAGER_REDUCTION)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    // must convert to skolem form
    Node t = ProofSkolemCache::getSkolemForm(args[0]);
    Node ret;
    if (id == PfRule::STRINGS_REDUCTION)
    {
      // TODO: eliminate optimizations
      SkolemCache sc;
      std::vector<Node> conj;
      ret = StringsPreprocess::reduce(t, conj, &sc);
      conj.push_back(t.eqNode(ret));
      ret = mkAnd(conj);
    }
    else if (id == PfRule::STRINGS_EAGER_REDUCTION)
    {
      ret = TermRegistry::eagerReduce(t);
    }
    if (ret.isNull())
    {
      return Node::null();
    }
    Node retw = ProofSkolemCache::getWitnessForm(ret);
    return retw;
  }
  else if (id == PfRule::RE_INTER)
  {
  }
  else if (id == PfRule::RE_UNFOLD_POS || id == PfRule::RE_UNFOLD_NEG)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node atom = children[0];
    if (id == PfRule::RE_UNFOLD_NEG)
    {
      if (atom.getKind() != NOT)
      {
        return Node::null();
      }
      atom = atom[0];
    }
    if (atom.getKind() != STRING_IN_REGEXP)
    {
      return Node::null();
    }
    // must convert to skolem form
    atom = ProofSkolemCache::getSkolemForm(atom);
    Node conc;
    SkolemCache sc;
    if (id == PfRule::RE_UNFOLD_POS)
    {
      conc = RegExpOpr::reduceRegExpPos(atom[0], atom[1], &sc);
    }
    else
    {
      conc = RegExpOpr::reduceRegExpNeg(atom[0], atom[1], &sc);
    }
    return ProofSkolemCache::getWitnessForm(conc);
  }
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
