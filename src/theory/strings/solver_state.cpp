/*********************                                                        */
/*! \file solver_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the solver state of the theory of strings.
 **/

#include "theory/strings/solver_state.h"

#include "theory/strings/theory_strings_utils.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

EqcInfo::EqcInfo(context::Context* c)
    : d_length_term(c),
      d_code_term(c),
      d_cardinality_lem_k(c),
      d_normalized_length(c),
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

SolverState::SolverState(context::Context* c, eq::EqualityEngine& ee)
    : d_context(c), d_ee(ee), d_conflict(c, false), d_pendingConflict(c)
{
}
SolverState::~SolverState()
{
  for (std::pair<const Node, EqcInfo*>& it : d_eqc_info)
  {
    delete it.second;
  }
}

Node SolverState::getRepresentative(Node t)
{
  if (d_ee.hasTerm(t))
  {
    return d_ee.getRepresentative(t);
  }
  return t;
}

bool SolverState::hasTerm(Node a) { return d_ee.hasTerm(a); }

bool SolverState::areEqual(Node a, Node b)
{
  if (a == b)
  {
    return true;
  }
  else if (hasTerm(a) && hasTerm(b))
  {
    return d_ee.areEqual(a, b);
  }
  return false;
}

bool SolverState::areDisequal(Node a, Node b)
{
  if (a == b)
  {
    return false;
  }
  else if (hasTerm(a) && hasTerm(b))
  {
    Node ar = d_ee.getRepresentative(a);
    Node br = d_ee.getRepresentative(b);
    return (ar != br && ar.isConst() && br.isConst())
           || d_ee.areDisequal(ar, br, false);
  }
  Node ar = getRepresentative(a);
  Node br = getRepresentative(b);
  return ar != br && ar.isConst() && br.isConst();
}

eq::EqualityEngine* SolverState::getEqualityEngine() const { return &d_ee; }

EqcInfo* SolverState::getOrMakeEqcInfo(Node eqc, bool doMake)
{
  std::map<Node, EqcInfo*>::iterator eqc_i = d_eqc_info.find(eqc);
  if (eqc_i != d_eqc_info.end())
  {
    return eqc_i->second;
  }
  if (doMake)
  {
    EqcInfo* ei = new EqcInfo(d_context);
    d_eqc_info[eqc] = ei;
    return ei;
  }
  return nullptr;
}

void SolverState::addEndpointsToEqcInfo(Node t, Node concat, Node eqc)
{
  Assert(concat.getKind() == STRING_CONCAT
         || concat.getKind() == REGEXP_CONCAT);
  EqcInfo* ei = nullptr;
  // check each side
  for (unsigned r = 0; r < 2; r++)
  {
    unsigned index = r == 0 ? 0 : concat.getNumChildren() - 1;
    Node c = utils::getConstantComponent(concat[index]);
    if (!c.isNull())
    {
      if (ei == nullptr)
      {
        ei = getOrMakeEqcInfo(eqc);
      }
      Trace("strings-eager-pconf-debug")
          << "New term: " << concat << " for " << t << " with prefix " << c
          << " (" << (r == 1) << ")" << std::endl;
      setPendingConflictWhen(ei->addEndpointConst(t, c, r == 1));
    }
  }
}

Node SolverState::getLengthExp(Node t, std::vector<Node>& exp, Node te)
{
  Assert(areEqual(t, te));
  Node lt = utils::mkLength(te);
  if (hasTerm(lt))
  {
    // use own length if it exists, leads to shorter explanation
    return lt;
  }
  EqcInfo* ei = getOrMakeEqcInfo(t, false);
  Node length_term = ei ? ei->d_length_term : Node::null();
  if (length_term.isNull())
  {
    // typically shouldnt be necessary
    length_term = t;
  }
  Debug("strings") << "SolverState::getLengthTerm " << t << " is "
                   << length_term << std::endl;
  if (te != length_term)
  {
    exp.push_back(te.eqNode(length_term));
  }
  return Rewriter::rewrite(
      NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, length_term));
}

Node SolverState::getLength(Node t, std::vector<Node>& exp)
{
  return getLengthExp(t, exp, t);
}

void SolverState::setConflict() { d_conflict = true; }
bool SolverState::isInConflict() const { return d_conflict; }

void SolverState::setPendingConflictWhen(Node conf)
{
  if (!conf.isNull() && d_pendingConflict.get().isNull())
  {
    d_pendingConflict = conf;
  }
}

Node SolverState::getPendingConflict() const { return d_pendingConflict; }

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
