/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for regular expression membership.
 */

#include "theory/strings/regexp_eval.h"

#include "theory/strings/theory_strings_utils.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * An NFA state.
 *
 * Edges can be annotated with constant characters, re.allchar or re.range
 * regular expressions.
 *
 * Regular expressions can be compiled to an NFA via construct. Evaluation
 * is computed via addToNext and processNextChar.
 */
class NfaState
{
 public:
  /**
   * Returns the NFA for regular expression r, connects the dangling arrows
   * to the given accept state.
   */
  static NfaState* construct(Node r,
                             NfaState* accept,
                             std::vector<std::shared_ptr<NfaState>>& scache)
  {
    NfaState* rs = constructInternal(r, scache);
    rs->connectTo(accept);
    return rs;
  }
  /**
   * Adds this state and all children connected by null to next.
   */
  void addToNext(std::unordered_set<NfaState*>& next)
  {
    // have property that all child states are also added to next if this
    // state has been added to next
    if (next.find(this) != next.end())
    {
      return;
    }
    next.insert(this);
    std::map<Node, std::vector<NfaState*>>::iterator it =
        d_children.find(Node::null());
    if (it != d_children.end())
    {
      for (NfaState* cs : it->second)
      {
        cs->addToNext(next);
      }
    }
  }
  /**
   * Processes the next input character nextChar from this state. Adds all
   * next states to process to the next set.
   */
  void processNextChar(unsigned nextChar, std::unordered_set<NfaState*>& next)
  {
    for (const std::pair<const Node, std::vector<NfaState*>>& c : d_children)
    {
      const Node& r = c.first;
      if (r.isNull())
      {
        continue;
      }
      bool accepts = false;
      switch (r.getKind())
      {
        case CONST_STRING:
          Assert(r.getConst<String>().size() == 1);
          accepts = (nextChar == r.getConst<String>().front());
          break;
        case REGEXP_RANGE:
        {
          unsigned a = r[0].getConst<String>().front();
          unsigned b = r[1].getConst<String>().front();
          accepts = (a <= nextChar && nextChar <= b);
        }
        break;
        case REGEXP_ALLCHAR: accepts = true; break;
        default: Unreachable() << "Unknown NFA edge " << c.first; break;
      }
      if (accepts)
      {
        for (NfaState* cs : c.second)
        {
          cs->addToNext(next);
        }
      }
    }
  }

 private:
  /**
   * Returns the (partial) NFA for regular expression r, whose dangling arrows
   * are in d_arrows of the returned NfaState.
   */
  static NfaState* constructInternal(
      Node r, std::vector<std::shared_ptr<NfaState>>& scache)
  {
    Kind k = r.getKind();
    // Concatenation does not introduce a new state, instead returns the
    // state of the first child.
    if (k == REGEXP_CONCAT)
    {
      NfaState* first = nullptr;
      NfaState* curr = nullptr;
      for (const Node& rc : r)
      {
        NfaState* rcs = constructInternal(rc, scache);
        if (first == nullptr)
        {
          first = rcs;
          curr = first;
          continue;
        }
        // connect previous to next
        curr->connectTo(rcs);
        // update current
        curr = rcs;
      }
      // should have had 2+ arguments
      Assert(curr != first && curr != nullptr && first != nullptr);
      // copy arrows from last to first
      first->d_arrows = curr->d_arrows;
      curr->d_arrows.clear();
      return first;
    }
    // Otherwise allocate a state.
    NfaState* s = allocateState(scache);
    std::vector<std::pair<NfaState*, Node>>& sarrows = s->d_arrows;
    switch (k)
    {
      case STRING_TO_REGEXP:
      {
        Assert(r[0].isConst());
        const String& str = r[0].getConst<String>();
        if (str.size() == 0)
        {
          // The regular expression is a no-op.
          sarrows.emplace_back(s, Node::null());
        }
        else
        {
          // this constructs N states in concatenation, where N is the length of
          // the string, each connected via single characters
          const std::vector<unsigned>& vec = str.getVec();
          NfaState* curr = s;
          NodeManager* nm = NodeManager::currentNM();
          for (size_t i = 0, nvec = vec.size(); i < nvec; i++)
          {
            std::vector<unsigned> charVec{vec[i]};
            Node nextChar = nm->mkConst(String(charVec));
            if (i + 1 == vec.size())
            {
              // the last edge is the dangling pointer of the first
              sarrows.emplace_back(curr, nextChar);
            }
            else
            {
              NfaState* next = allocateState(scache);
              curr->d_children[nextChar].push_back(next);
              curr = next;
            }
          }
        }
      }
      break;
      case REGEXP_ALLCHAR:
      case REGEXP_RANGE: sarrows.emplace_back(s, r); break;
      case REGEXP_UNION:
      {
        // connect to all children via null, take union of arrows
        std::vector<NfaState*>& schildren = s->d_children[Node::null()];
        for (const Node& rc : r)
        {
          NfaState* rcs = constructInternal(rc, scache);
          schildren.push_back(rcs);
          std::vector<std::pair<NfaState*, Node>>& rcsarrows = rcs->d_arrows;
          sarrows.insert(sarrows.end(), rcsarrows.begin(), rcsarrows.end());
          rcsarrows.clear();
        }
      }
      break;
      case REGEXP_STAR:
      {
        NfaState* body = constructInternal(r[0], scache);
        s->d_children[Node::null()].push_back(body);
        // body loops back to this state
        body->connectTo(s);
        // skip moves on
        sarrows.emplace_back(s, Node::null());
      }
      break;
      default: Unreachable() << "Unknown regular expression " << r; break;
    }
    return s;
  }
  /** Connect dangling arrows of this to state s and clear */
  void connectTo(NfaState* s)
  {
    for (std::pair<NfaState*, Node>& a : d_arrows)
    {
      a.first->d_children[a.second].push_back(s);
    }
    d_arrows.clear();
  }
  /** Allocate state, add to cache (for memory management) */
  static NfaState* allocateState(std::vector<std::shared_ptr<NfaState>>& scache)
  {
    std::shared_ptr<NfaState> ret = std::make_shared<NfaState>();
    scache.push_back(ret);
    return ret.get();
  }
  /**
   * Edges from this state. Maps constant characters, re.allchar or re.range
   * to the list of children connected via an edge with that label.
   */
  std::map<Node, std::vector<NfaState*>> d_children;
  /** Current dangling pointers */
  std::vector<std::pair<NfaState*, Node>> d_arrows;
};

bool RegExpEval::canEvaluate(const Node& r)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(r);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // if not already visited
    if (visited.insert(cur).second)
    {
      switch (cur.getKind())
      {
        case STRING_TO_REGEXP:
          if (!cur[0].isConst())
          {
            return false;
          }
          break;
        case REGEXP_RANGE:
          if (!utils::isCharacterRange(cur))
          {
            return false;
          }
          break;
        case REGEXP_ALLCHAR: break;
        case REGEXP_UNION:
        case REGEXP_CONCAT:
        case REGEXP_STAR:
          for (const Node& cc : cur)
          {
            visit.push_back(cc);
          }
          break;
        default: return false;
      }
    }
  } while (!visit.empty());
  return true;
}

bool RegExpEval::evaluate(String& s, const Node& r)
{
  Trace("re-eval") << "Evaluate " << s << " in " << r << std::endl;
  // no intersection, complement, and r must be constant.
  Assert(canEvaluate(r));
  NfaState accept;
  std::vector<std::shared_ptr<NfaState>> scache;
  NfaState* rs = NfaState::construct(r, &accept, scache);
  Trace("re-eval") << "NFA size is " << (scache.size() + 1) << std::endl;
  std::unordered_set<NfaState*> curr;
  rs->addToNext(curr);
  const std::vector<unsigned>& vec = s.getVec();
  for (size_t i = 0, nvec = vec.size(); i < nvec; i++)
  {
    Trace("re-eval") << "..process next char " << vec[i]
                     << ", #states=" << curr.size() << std::endl;
    std::unordered_set<NfaState*> next;
    for (NfaState* cs : curr)
    {
      cs->processNextChar(vec[i], next);
    }
    // if there are no more states, we are done
    if (next.empty())
    {
      return false;
    }
    curr = next;
  }
  Trace("re-eval") << "..finish #states=" << curr.size() << std::endl;
  return curr.find(&accept) != curr.end();
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
