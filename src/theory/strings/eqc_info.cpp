/*********************                                                        */
/*! \file eqc_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equivalence class info for the theory of strings
 **/

#include "theory/strings/eqc_info.h"

#include "theory/strings/theory_strings_utils.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

EqcInfo::EqcInfo(context::Context* c)
    : d_lengthTerm(c),
      d_codeTerm(c),
      d_cardinalityLemK(c),
      d_normalizedLength(c),
      d_prefixC(c),
      d_suffixC(c)
{
}

Node EqcInfo::addEndpointConst(Node t, Node c, bool isSuf)
{
  // check conflict
  Node prev = isSuf ? d_suffixC : d_prefixC;
  if (!prev.isNull())
  {
    Trace("strings-eager-pconf-debug") << "Check conflict " << prev << ", " << t
                                       << " post=" << isSuf << std::endl;
    Node prevC = utils::getConstantEndpoint(prev, isSuf);
    Assert(!prevC.isNull());
    Assert(prevC.getKind() == CONST_STRING);
    if (c.isNull())
    {
      c = utils::getConstantEndpoint(t, isSuf);
      Assert(!c.isNull());
    }
    Assert(c.getKind() == CONST_STRING);
    bool conflict = false;
    // if the constant prefixes are different
    if (c != prevC)
    {
      // conflicts between constants should be handled by equality engine
      Assert(!t.isConst() || !prev.isConst());
      Trace("strings-eager-pconf-debug")
          << "Check conflict constants " << prevC << ", " << c << std::endl;
      const String& ps = prevC.getConst<String>();
      const String& cs = c.getConst<String>();
      unsigned pvs = ps.size();
      unsigned cvs = cs.size();
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
        const String& larges = pvs > cvs ? ps : cs;
        const String& smalls = pvs > cvs ? cs : ps;
        if (isSuf)
        {
          conflict = !larges.hasSuffix(smalls);
        }
        else
        {
          conflict = !larges.hasPrefix(smalls);
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
      std::vector<Node> ccs;
      Node r[2];
      for (unsigned i = 0; i < 2; i++)
      {
        Node tp = i == 0 ? t : prev;
        if (tp.getKind() == STRING_IN_REGEXP)
        {
          ccs.push_back(tp);
          r[i] = tp[0];
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
      Node ret =
          ccs.size() == 1 ? ccs[0] : NodeManager::currentNM()->mkNode(AND, ccs);
      Trace("strings-eager-pconf")
          << "String: eager prefix conflict: " << ret << std::endl;
      return ret;
    }
  }
  if (isSuf)
  {
    d_suffixC = t;
  }
  else
  {
    d_prefixC = t;
  }
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
