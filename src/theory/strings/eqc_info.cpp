/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equivalence class info for the theory of strings.
 */

#include "theory/strings/eqc_info.h"

#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

EqcInfo::EqcInfo(context::Context* c)
    : d_lengthTerm(c),
      d_codeTerm(c),
      d_cardinalityLemK(c),
      d_normalizedLength(c),
      d_firstBound(c),
      d_secondBound(c)
{
}

Node EqcInfo::addEndpointConst(Node t, Node c, bool isSuf)
{
  // check conflict
  Node prev = isSuf ? d_secondBound : d_firstBound;
  if (!prev.isNull())
  {
    Trace("strings-eager-pconf-debug") << "Check conflict " << prev << ", " << t
                                       << " post=" << isSuf << std::endl;
    Node prevC = utils::getConstantEndpoint(prev, isSuf);
    Assert(!prevC.isNull());
    Assert(prevC.isConst());
    if (c.isNull())
    {
      c = utils::getConstantEndpoint(t, isSuf);
      Assert(!c.isNull());
    }
    Assert(c.isConst());
    bool conflict = false;
    // if the constant prefixes are different
    if (c != prevC)
    {
      // conflicts between constants should be handled by equality engine
      Assert(!t.isConst() || !prev.isConst());
      Trace("strings-eager-pconf-debug")
          << "Check conflict constants " << prevC << ", " << c << std::endl;
      size_t pvs = Word::getLength(prevC);
      size_t cvs = Word::getLength(c);
      if (pvs == cvs || (pvs > cvs && t.isConst())
          || (cvs > pvs && prev.isConst()))
      {
        // If equal length, cannot be equal due to node check above.
        // If one is fully constant and has less length than the other, then the
        // other will not fit and we are in conflict.
        conflict = true;
      }
      else
      {
        Node larges = pvs > cvs ? prevC : c;
        Node smalls = pvs > cvs ? c : prevC;
        if (isSuf)
        {
          conflict = !Word::hasSuffix(larges, smalls);
        }
        else
        {
          conflict = !Word::hasPrefix(larges, smalls);
        }
      }
      if (!conflict && (pvs > cvs || prev.isConst()))
      {
        // current is subsumed, either shorter prefix or the other is a full
        // constant
        return Node::null();
      }
    }
    else if (!t.isConst())
    {
      // current is subsumed since the other may be a full constant
      return Node::null();
    }
    if (conflict)
    {
      Trace("strings-eager-pconf")
          << "Conflict for " << prevC << ", " << c << std::endl;
      Node ret = mkMergeConflict(t, prev, false);
      Trace("strings-eager-pconf")
          << "String: eager prefix conflict: " << ret << std::endl;
      return ret;
    }
  }
  if (isSuf)
  {
    d_secondBound = t;
  }
  else
  {
    d_firstBound = t;
  }
  return Node::null();
}

Node EqcInfo::mkMergeConflict(Node t, Node prev, bool isArith)
{
  Trace("strings-eager-debug")
      << "mkMergeConflict " << t << ", " << prev << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> ccs;
  Node r[2];
  for (unsigned i = 0; i < 2; i++)
  {
    Node tp = i == 0 ? t : prev;
    if (tp.getKind() == STRING_IN_REGEXP)
    {
      ccs.push_back(tp);
      r[i] = isArith ? nm->mkNode(STRING_LENGTH, tp[0]) : tp[0];
    }
    else
    {
      r[i] = tp;
    }
  }
  if (r[0] != r[1])
  {
    ccs.push_back(r[0].eqNode(r[1]));
  }
  Assert(!ccs.empty());
  return nm->mkAnd(ccs);
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
