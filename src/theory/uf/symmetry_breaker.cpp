/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of algorithm suggested by Deharbe, Fontaine, Merz,
 * and Paleo, "Exploiting symmetry in SMT problems," CADE 2011.
 *
 * From the paper:
 *
 * <pre>
 *   \f$ P := guess\_permutations(\phi) \f$
 *   foreach \f$ {c_0, ..., c_n} \in P \f$ do
 *     if \f$ invariant\_by\_permutations(\phi, {c_0, ..., c_n}) \f$ then
 *       T := \f$ select\_terms(\phi, {c_0, ..., c_n}) \f$
 *       cts := \f$ \emptyset \f$
 *       while T != \f$ \empty \wedge |cts| <= n \f$ do
 *         \f$ t := select\_most\_promising\_term(T, \phi) \f$
 *         \f$ T := T \setminus {t} \f$
 *         cts := cts \f$ \cup used\_in(t, {c_0, ..., c_n}) \f$
 *         let \f$ c \in {c_0, ..., c_n} \setminus cts \f$
 *         cts := cts \f$ \cup {c} \f$
 *         if cts != \f$ {c_0, ..., c_n} \f$ then
 *           \f$ \phi := \phi \wedge ( \vee_{c_i \in cts} t = c_i ) \f$
 *         end
 *       end
 *     end
 *   end
 *   return \f$ \phi \f$
 * </pre>
 */

#include "theory/uf/symmetry_breaker.h"

#include <iterator>
#include <queue>

#include "theory/rewriter.h"
#include "util/hash.h"
#include "util/statistics_registry.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace uf {

using namespace cvc5::context;

SymmetryBreaker::Template::Template() :
  d_template(),
  d_sets(),
  d_reps() {
}

TNode SymmetryBreaker::Template::find(TNode n) {
  unordered_map<TNode, TNode>::iterator i = d_reps.find(n);
  if(i == d_reps.end()) {
    return n;
  } else {
    return d_reps[n] = find((*i).second);
  }
}

bool SymmetryBreaker::Template::matchRecursive(TNode t, TNode n) {
  IndentedScope scope(Trace("ufsymm:match"));

  Trace("ufsymm:match") << "UFSYMM matching " << t << endl
                        << "UFSYMM       to " << n << endl;

  if(t.getKind() != n.getKind() || t.getNumChildren() != n.getNumChildren()) {
    Trace("ufsymm:match") << "UFSYMM BAD MATCH on kind, #children" << endl;
    return false;
  }

  if(t.getNumChildren() == 0) {
    if (!t.isVar())
    {
      Trace("ufsymm:match") << "UFSYMM non-variables, failing match" << endl;
      return false;
    }
    t = find(t);
    n = find(n);
    Trace("ufsymm:match") << "UFSYMM variable match " << t << " , " << n << endl;
    Trace("ufsymm:match") << "UFSYMM sets: " << t << " =>";
    if(d_sets.find(t) != d_sets.end()) {
      for(set<TNode>::iterator i = d_sets[t].begin(); i != d_sets[t].end(); ++i) {
        Trace("ufsymm:match") << " " << *i;
      }
    }
    Trace("ufsymm:match") << endl;
    if(t != n) {
      Trace("ufsymm:match") << "UFSYMM sets: " << n << " =>";
      if(d_sets.find(n) != d_sets.end()) {
        for(set<TNode>::iterator i = d_sets[n].begin(); i != d_sets[n].end(); ++i) {
          Trace("ufsymm:match") << " " << *i;
        }
      }
      Trace("ufsymm:match") << endl;

      if(d_sets.find(t) == d_sets.end()) {
        Trace("ufsymm:match") << "UFSYMM inserting " << t << " in with " << n << endl;
        d_reps[t] = n;
        d_sets[n].insert(t);
      } else {
        if(d_sets.find(n) != d_sets.end()) {
          Trace("ufsymm:match") << "UFSYMM merging " << n << " and " << t << " in with " << n << endl;
          d_sets[n].insert(d_sets[t].begin(), d_sets[t].end());
          d_sets[n].insert(t);
          d_reps[t] = n;
          d_sets.erase(t);
        } else {
          Trace("ufsymm:match") << "UFSYMM inserting " << n << " in with " << t << endl;
          d_sets[t].insert(n);
          d_reps[n] = t;
        }
      }
    }
    return true;
  }

  if(t.getMetaKind() == kind::metakind::PARAMETERIZED) {
    if(t.getOperator() != n.getOperator()) {
      Trace("ufsymm:match") << "UFSYMM BAD MATCH on operators: " << t.getOperator() << " != " << n.getOperator() << endl;
      return false;
    }
  }
  TNode::iterator ti = t.begin();
  TNode::iterator ni = n.begin();
  while(ti != t.end()) {
    if(*ti != *ni) { // nothing to do if equal
      if(!matchRecursive(*ti, *ni)) {
        Trace("ufsymm:match") << "UFSYMM BAD MATCH, withdrawing.." << endl;
        return false;
      }
    }
    ++ti;
    ++ni;
  }

  return true;
}

bool SymmetryBreaker::Template::match(TNode n) {
  // try to "match" n and d_template
  if(d_template.isNull()) {
    Trace("ufsymm") << "UFSYMM setting template " << n << endl;
    d_template = n;
    return true;
  } else {
    return matchRecursive(d_template, n);
  }
}

void SymmetryBreaker::Template::reset() {
  d_template = Node::null();
  d_sets.clear();
  d_reps.clear();
}

SymmetryBreaker::SymmetryBreaker(Env& env, std::string name)
    : EnvObj(env),
      ContextNotifyObj(userContext()),
      d_assertionsToRerun(userContext()),
      d_rerunningAssertions(false),
      d_phi(),
      d_phiSet(),
      d_permutations(),
      d_terms(),
      d_template(),
      d_normalizationCache(),
      d_termEqs(),
      d_termEqsOnly(),
      d_name(name),
      d_stats(statisticsRegistry(), d_name + "theory::uf::symmetry_breaker::")
{
}

class SBGuard {
  bool& d_ref;
  bool d_old;
public:
  SBGuard(bool& b) : d_ref(b), d_old(b) {}
  ~SBGuard() { Trace("uf") << "reset to " << d_old << std::endl; d_ref = d_old; }
};/* class SBGuard */

void SymmetryBreaker::rerunAssertionsIfNecessary() {
  if(d_rerunningAssertions || !d_phi.empty() || d_assertionsToRerun.empty()) {
    return;
  }

  SBGuard g(d_rerunningAssertions);
  d_rerunningAssertions = true;

  Trace("ufsymm") << "UFSYMM: rerunning assertions..." << std::endl;
  for(CDList<Node>::const_iterator i = d_assertionsToRerun.begin();
      i != d_assertionsToRerun.end();
      ++i) {
    assertFormula(*i);
  }
  Trace("ufsymm") << "UFSYMM: DONE rerunning assertions..." << std::endl;
}

Node SymmetryBreaker::norm(TNode phi) {
  Node n = rewrite(phi);
  return normInternal(n, 0);
}

Node SymmetryBreaker::normInternal(TNode n, size_t level) {
  Node& result = d_normalizationCache[n];
  if(!result.isNull()) {
    return result;
  }

  switch(Kind k = n.getKind()) {

  case kind::DISTINCT: {
    // commutative N-ary operator handling
    vector<TNode> kids(n.begin(), n.end());
    sort(kids.begin(), kids.end());
    return result = NodeManager::currentNM()->mkNode(k, kids);
  }

  case kind::AND: {
    // commutative+associative N-ary operator handling
    vector<Node> kids;
    kids.reserve(n.getNumChildren());
    queue<TNode> work;
    work.push(n);
    Trace("ufsymm:norm") << "UFSYMM processing " << n << endl;
    do {
      TNode m = work.front();
      work.pop();
      for(TNode::iterator i = m.begin(); i != m.end(); ++i) {
        if((*i).getKind() == k) {
          work.push(*i);
        } else {
          if( (*i).getKind() == kind::OR ) {
            kids.push_back(normInternal(*i, level));
          } else if((*i).getKind() == kind::EQUAL) {
            kids.push_back(normInternal(*i, level));
            if((*i)[0].isVar() ||
               (*i)[1].isVar()) {
              d_termEqs[(*i)[0]].insert((*i)[1]);
              d_termEqs[(*i)[1]].insert((*i)[0]);
              if(level == 0) {
                d_termEqsOnly[(*i)[0]].insert((*i)[1]);
                d_termEqsOnly[(*i)[1]].insert((*i)[0]);
                Trace("ufsymm:eq") << "UFSYMM " << (*i)[0] << " <==> " << (*i)[1] << endl;
              }
            }
          } else {
            kids.push_back(*i);
          }
        }
      }
    } while(!work.empty());
    Trace("ufsymm:norm") << "UFSYMM got " << kids.size() << " kids for the " << k << "-kinded Node" << endl;
    sort(kids.begin(), kids.end());
    return result = NodeManager::currentNM()->mkNode(k, kids);
  }

  case kind::OR: {
    // commutative+associative N-ary operator handling
    vector<Node> kids;
    kids.reserve(n.getNumChildren());
    queue<TNode> work;
    work.push(n);
    Trace("ufsymm:norm") << "UFSYMM processing " << n << endl;
    TNode matchingTerm = TNode::null();
    vector<TNode> matchingTermEquals;
    bool first = true, matchedVar = false;
    do {
      TNode m = work.front();
      work.pop();
      for(TNode::iterator i = m.begin(); i != m.end(); ++i) {
        if((*i).getKind() == k) {
          work.push(*i);
        } else {
          if( (*i).getKind() == kind::AND ) {
            first = false;
            matchingTerm = TNode::null();
            kids.push_back(normInternal(*i, level + 1));
          } else if((*i).getKind() == kind::EQUAL) {
            kids.push_back(normInternal(*i, level + 1));
            if((*i)[0].isVar() ||
               (*i)[1].isVar()) {
              d_termEqs[(*i)[0]].insert((*i)[1]);
              d_termEqs[(*i)[1]].insert((*i)[0]);
              if(level == 0) {
                if(first) {
                  matchingTerm = *i;
                } else if(!matchingTerm.isNull()) {
                  if(matchedVar) {
                    if(matchingTerm == (*i)[0]) {
                      matchingTermEquals.push_back((*i)[1]);
                    } else if(matchingTerm == (*i)[1]) {
                      matchingTermEquals.push_back((*i)[0]);
                    } else {
                      matchingTerm = TNode::null();
                    }
                  } else if((*i)[0] == matchingTerm[0]) {
                    matchingTermEquals.push_back(matchingTerm[1]);
                    matchingTermEquals.push_back((*i)[1]);
                    matchingTerm = matchingTerm[0];
                    matchedVar = true;
                  } else if((*i)[1] == matchingTerm[0]) {
                    matchingTermEquals.push_back(matchingTerm[1]);
                    matchingTermEquals.push_back((*i)[0]);
                    matchingTerm = matchingTerm[0];
                    matchedVar = true;
                  } else if((*i)[0] == matchingTerm[1]) {
                    matchingTermEquals.push_back(matchingTerm[0]);
                    matchingTermEquals.push_back((*i)[1]);
                    matchingTerm = matchingTerm[1];
                    matchedVar = true;
                  } else if((*i)[1] == matchingTerm[1]) {
                    matchingTermEquals.push_back(matchingTerm[0]);
                    matchingTermEquals.push_back((*i)[0]);
                    matchingTerm = matchingTerm[1];
                    matchedVar = true;
                  } else {
                    matchingTerm = TNode::null();
                  }
                }
              }
            } else {
              matchingTerm = TNode::null();
            }
            first = false;
          } else {
            first = false;
            matchingTerm = TNode::null();
            kids.push_back(*i);
          }
        }
      }
    } while(!work.empty());
    if(!matchingTerm.isNull()) {
      if(TraceIsOn("ufsymm:eq")) {
        Trace("ufsymm:eq") << "UFSYMM here we can conclude that " << matchingTerm << " is one of {";
        for(vector<TNode>::const_iterator i = matchingTermEquals.begin(); i != matchingTermEquals.end(); ++i) {
          Trace("ufsymm:eq") << " " << *i;
        }
        Trace("ufsymm:eq") << " }" << endl;
      }
      d_termEqsOnly[matchingTerm].insert(matchingTermEquals.begin(), matchingTermEquals.end());
    }
    Trace("ufsymm:norm") << "UFSYMM got " << kids.size() << " kids for the " << k << "-kinded Node" << endl;
    sort(kids.begin(), kids.end());
    return result = NodeManager::currentNM()->mkNode(k, kids);
  }
  
  case kind::EQUAL:
    if(n[0].isVar() ||
       n[1].isVar()) {
      d_termEqs[n[0]].insert(n[1]);
      d_termEqs[n[1]].insert(n[0]);
      if(level == 0) {
        d_termEqsOnly[n[0]].insert(n[1]);
        d_termEqsOnly[n[1]].insert(n[0]);
        Trace("ufsymm:eq") << "UFSYMM " << n[0] << " <==> " << n[1] << endl;
      }
    }
    CVC5_FALLTHROUGH;
  case kind::XOR:
    // commutative binary operator handling
    return n[1] < n[0] ? NodeManager::currentNM()->mkNode(k, n[1], n[0]) : Node(n);

  default:
    // Normally T-rewriting is enough; only special cases (like
    // Boolean-layer stuff) has to go above.
    return n;
  }
}

void SymmetryBreaker::assertFormula(TNode phi) {
  rerunAssertionsIfNecessary();
  if(!d_rerunningAssertions) {
    d_assertionsToRerun.push_back(phi);
  }
  // use d_phi, put into d_permutations
  Trace("ufsymm") << "UFSYMM assertFormula(): phi is " << phi << endl;
  d_phi.push_back(phi);
  if(phi.getKind() == kind::OR) {
    Template t;
    Node::iterator i = phi.begin();
    t.match(*i++);
    while(i != phi.end()) {
      if(!t.match(*i++)) {
        break;
      }
    }
    unordered_map<TNode, set<TNode>>& ps = t.partitions();
    for (auto& kv : ps)
    {
      Trace("ufsymm") << "UFSYMM partition*: " << kv.first;
      set<TNode>& p = kv.second;
      for(set<TNode>::iterator j = p.begin();
          j != p.end();
          ++j) {
        Trace("ufsymm") << " " << *j;
      }
      Trace("ufsymm") << endl;
      p.insert(kv.first);
      Permutations::iterator pi = d_permutations.find(p);
      if(pi == d_permutations.end()) {
        d_permutations.insert(p);
      }
    }
  }
  if(!d_template.match(phi)) {
    // we hit a bad match, extract the partitions and reset the template
    unordered_map<TNode, set<TNode>>& ps = d_template.partitions();
    Trace("ufsymm") << "UFSYMM hit a bad match---have " << ps.size() << " partitions:" << endl;
    for (unordered_map<TNode, set<TNode>>::iterator i = ps.begin();
         i != ps.end();
         ++i)
    {
      Trace("ufsymm") << "UFSYMM partition: " << (*i).first;
      set<TNode>& p = (*i).second;
      if(TraceIsOn("ufsymm")) {
        for(set<TNode>::iterator j = p.begin();
            j != p.end();
            ++j) {
          Trace("ufsymm") << " " << *j;
        }
      }
      Trace("ufsymm") << endl;
      p.insert((*i).first);
      d_permutations.insert(p);
    }
    d_template.reset();
    bool good CVC5_UNUSED = d_template.match(phi);
    Assert(good);
  }
}

void SymmetryBreaker::clear() {
  d_phi.clear();
  d_phiSet.clear();
  d_permutations.clear();
  d_terms.clear();
  d_template.reset();
  d_normalizationCache.clear();
  d_termEqs.clear();
  d_termEqsOnly.clear();
}

void SymmetryBreaker::apply(std::vector<Node>& newClauses) {
  rerunAssertionsIfNecessary();
  guessPermutations();
  Trace("ufsymm") << "UFSYMM =====================================================" << endl
                  << "UFSYMM have " << d_permutations.size() << " permutation sets" << endl;
  if(!d_permutations.empty()) {
    { TimerStat::CodeTimer codeTimer(d_stats.d_initNormalizationTimer);
      // normalize d_phi

      for(vector<Node>::iterator i = d_phi.begin(); i != d_phi.end(); ++i) {
        Node n = *i;
        *i = norm(n);
        d_phiSet.insert(*i);
        Trace("ufsymm:norm") << "UFSYMM init-norm-rewrite " << n << endl
                             << "UFSYMM                to " << *i << endl;
      }
    }

    for (const Permutation& p : d_permutations)
    {
      ++(d_stats.d_permutationSetsConsidered);
      Trace("ufsymm") << "UFSYMM looking at permutation: " << p << endl;
      size_t n = p.size() - 1;
      if(invariantByPermutations(p)) {
        ++(d_stats.d_permutationSetsInvariant);
        selectTerms(p);
        set<Node> cts;
        while(!d_terms.empty() && cts.size() <= n) {
          Trace("ufsymm") << "UFSYMM ==== top of loop, d_terms.size() == " << d_terms.size() << " , cts.size() == " << cts.size() << " , n == " << n << endl;
          Terms::iterator ti = selectMostPromisingTerm(d_terms);
          Node t = *ti;
          Trace("ufsymm") << "UFSYMM promising term is " << t << endl;
          d_terms.erase(ti);
          insertUsedIn(t, p, cts);
          if(TraceIsOn("ufsymm")) {
            if(cts.empty()) {
              Trace("ufsymm") << "UFSYMM cts is empty" << endl;
            } else {
              for(set<Node>::iterator ctsi = cts.begin(); ctsi != cts.end(); ++ctsi) {
                Trace("ufsymm") << "UFSYMM cts: " << *ctsi << endl;
              }
            }
          }
          TNode c;
          Trace("ufsymm") << "UFSYMM looking for c \\in " << p << " \\ cts" << endl;
          set<TNode>::const_iterator i;
          for(i = p.begin(); i != p.end(); ++i) {
            if(cts.find(*i) == cts.end()) {
              if(c.isNull()) {
                c = *i;
                Trace("ufsymm") << "UFSYMM found first: " << c << endl;
              } else {
                Trace("ufsymm") << "UFSYMM found second: " << *i << endl;
                break;
              }
            }
          }
          if(c.isNull()) {
            Trace("ufsymm") << "UFSYMM can't find a c, restart outer loop" << endl;
            break;
          }
          Trace("ufsymm") << "UFSYMM inserting into cts: " << c << endl;
          cts.insert(c);
          // This tests cts != p: if "i == p.end()", we got all the way
          // through p without seeing two elements not in cts (on the
          // second one, we break from the above loop).  We know we
          // found at least one (and subsequently added it to cts).  So
          // now cts == p.
          Trace("ufsymm") << "UFSYMM p == " << p << endl;
          if(i != p.end() || p.size() != cts.size()) {
            Trace("ufsymm") << "UFSYMM cts != p" << endl;
            NodeBuilder disj(kind::OR);
            NodeManager* nm = NodeManager::currentNM();
            for (const Node& nn : cts)
            {
              if (t != nn)
              {
                disj << nm->mkNode(kind::EQUAL, t, nn);
              }
            }
            Node d;
            if(disj.getNumChildren() > 1) {
              d = disj;
              ++(d_stats.d_clauses);
            } else {
              d = disj[0];
              disj.clear();
              ++(d_stats.d_units);
            }
            if(TraceIsOn("ufsymm")) {
              Trace("ufsymm") << "UFSYMM symmetry-breaking clause: " << d << endl;
            } else {
              Trace("ufsymm:clauses") << "UFSYMM symmetry-breaking clause: " << d << endl;
            }
            newClauses.push_back(d);
          } else {
            Trace("ufsymm") << "UFSYMM cts == p" << endl;
          }
          Trace("ufsymm") << "UFSYMM ==== end of loop, d_terms.size() == " << d_terms.size() << " , cts.size() == " << cts.size() << " , n == " << n << endl;
        }
      }
    }
  }

  clear();
}

void SymmetryBreaker::guessPermutations() {
  // use d_phi, put into d_permutations
  Trace("ufsymm") << "UFSYMM guessPermutations()" << endl;
}

bool SymmetryBreaker::invariantByPermutations(const Permutation& p) {
  TimerStat::CodeTimer codeTimer(d_stats.d_invariantByPermutationsTimer);

  // use d_phi
  Trace("ufsymm") << "UFSYMM invariantByPermutations()? " << p << endl;

  Assert(p.size() > 1);

  // check that the types match
  Permutation::iterator permIt = p.begin();
  TypeNode type = (*permIt++).getType();
  do {
    if(type != (*permIt++).getType()) {
      Trace("ufsymm") << "UFSYMM types don't match, aborting.." << endl;
      return false;
    }
  } while(permIt != p.end());

  // check P_swap
  vector<Node> subs;
  vector<Node> repls;
  Permutation::iterator i = p.begin();
  TNode p0 = *i++;
  TNode p1 = *i;
  subs.push_back(p0);
  subs.push_back(p1);
  repls.push_back(p1);
  repls.push_back(p0);
  for (const Node& nn : d_phi)
  {
    Node s =
        nn.substitute(subs.begin(), subs.end(), repls.begin(), repls.end());
    Node n = norm(s);
    if (nn != n && d_phiSet.find(n) == d_phiSet.end())
    {
      Trace("ufsymm")
          << "UFSYMM P_swap is NOT an inv perm op for " << p << endl
          << "UFSYMM because this node: " << nn << endl
          << "UFSYMM rewrite-norms to : " << n << endl
          << "UFSYMM which is not in our set of normalized assertions" << endl;
      return false;
    }
    else if (TraceIsOn("ufsymm:p"))
    {
      if (nn == s)
      {
        Trace("ufsymm:p") << "UFSYMM P_swap passes trivially: " << nn << endl;
      }
      else
      {
        Trace("ufsymm:p") << "UFSYMM P_swap passes: " << nn << endl
                          << "UFSYMM      rewrites: " << s << endl
                          << "UFSYMM         norms: " << n << endl;
      }
    }
  }
  Trace("ufsymm") << "UFSYMM P_swap is an inv perm op for " << p << endl;

  // check P_circ, unless size == 2 in which case P_circ == P_swap
  if(p.size() > 2) {
    subs.clear();
    repls.clear();
    bool first = true;
    for (TNode nn : p)
    {
      subs.push_back(nn);
      if(!first) {
        repls.push_back(nn);
      } else {
        first = false;
      }
    }
    repls.push_back(*p.begin());
    Assert(subs.size() == repls.size());
    for (const Node& nn : d_phi)
    {
      Node s =
          nn.substitute(subs.begin(), subs.end(), repls.begin(), repls.end());
      Node n = norm(s);
      if (nn != n && d_phiSet.find(n) == d_phiSet.end())
      {
        Trace("ufsymm")
            << "UFSYMM P_circ is NOT an inv perm op for " << p << endl
            << "UFSYMM because this node: " << nn << endl
            << "UFSYMM rewrite-norms to : " << n << endl
            << "UFSYMM which is not in our set of normalized assertions"
            << endl;
        return false;
      }
      else if (TraceIsOn("ufsymm:p"))
      {
        if (nn == s)
        {
          Trace("ufsymm:p") << "UFSYMM P_circ passes trivially: " << nn << endl;
        }
        else
        {
          Trace("ufsymm:p") << "UFSYMM P_circ passes: " << nn << endl
                            << "UFSYMM      rewrites: " << s << endl
                            << "UFSYMM         norms: " << n << endl;
        }
      }
    }
    Trace("ufsymm") << "UFSYMM P_circ is an inv perm op for " << p << endl;
  } else {
    Trace("ufsymm") << "UFSYMM no need to check P_circ, since P_circ == P_swap for perm sets of size 2" << endl;
  }

  return true;
}

// debug-assertion-only function
template <class T1, class T2>
static bool isSubset(const T1& s, const T2& t) {
  if(s.size() > t.size()) {
    //Trace("ufsymm") << "DEBUG ASSERTION FAIL: s not a subset of t "
    //                << "because size(s) > size(t)" << endl;
    return false;
  }
  for(typename T1::const_iterator si = s.begin(); si != s.end(); ++si) {
    if(t.find(*si) == t.end()) {
      //Trace("ufsymm") << "DEBUG ASSERTION FAIL: s not a subset of t "
      //                << "because s element \"" << *si << "\" not in t" << endl;
      return false;
    }
  }

  // At this point, didn't find any elements from s not in t, so
  // conclude that s \subseteq t
  return true;
}

void SymmetryBreaker::selectTerms(const Permutation& p) {
  TimerStat::CodeTimer codeTimer(d_stats.d_selectTermsTimer);

  // use d_phi, put into d_terms
  Trace("ufsymm") << "UFSYMM selectTerms(): " << p << endl;
  d_terms.clear();
  set<Node> terms;
  for(Permutation::iterator i = p.begin(); i != p.end(); ++i) {
    const TermEq& teq = d_termEqs[*i];
    for(TermEq::const_iterator j = teq.begin(); j != teq.end(); ++j) {
      Trace("ufsymm") << "selectTerms: insert in terms " << *j << std::endl;
    }
    terms.insert(teq.begin(), teq.end());
  }
  for(set<Node>::iterator i = terms.begin(); i != terms.end(); ++i) {
    if(d_termEqsOnly.find(*i) != d_termEqsOnly.end()) {
      const TermEq& teq = d_termEqsOnly[*i];
      if(isSubset(teq, p)) {
        Trace("ufsymm") << "selectTerms: teq = {";
        for(TermEq::const_iterator j = teq.begin(); j != teq.end(); ++j) {
          Trace("ufsymm") << " " << *j << std::endl;
        }
        Trace("ufsymm") << " } is subset of p " << p << std::endl;
        d_terms.insert(d_terms.end(), *i);
      } else {
        if(TraceIsOn("ufsymm")) {
          Trace("ufsymm") << "UFSYMM selectTerms() threw away candidate: " << *i << endl;
          Trace("ufsymm:eq") << "UFSYMM selectTerms() #teq == " << teq.size() << " #p == " << p.size() << endl;
          TermEq::iterator j;
          for(j = teq.begin(); j != teq.end(); ++j) {
            Trace("ufsymm:eq") << "UFSYMM              -- teq " << *j << " in " << p << " ?" << endl;
            if(p.find(*j) == p.end()) {
              Trace("ufsymm") << "UFSYMM              -- because its teq " << *j
                              << " isn't in " << p << endl;
              break;
            } else {
              Trace("ufsymm:eq") << "UFSYMM              -- yep" << endl;
            }
          }
          Assert(j != teq.end())
              << "failed to find a difference between p and teq ?!";
        }
      }
    } else {
      Trace("ufsymm") << "selectTerms: don't have data for " << *i << " so can't conclude anything" << endl;
    }
  }
  if(TraceIsOn("ufsymm")) {
    for(list<Term>::iterator i = d_terms.begin(); i != d_terms.end(); ++i) {
      Trace("ufsymm") << "UFSYMM selectTerms() returning: " << *i << endl;
    }
  }
}

SymmetryBreaker::Statistics::Statistics(StatisticsRegistry& sr,
                                        const std::string& name)
    : d_clauses(sr.registerInt(name + "clauses")),
      d_units(sr.registerInt(name + "units")),
      d_permutationSetsConsidered(
          sr.registerInt(name + "permutationSetsConsidered")),
      d_permutationSetsInvariant(
          sr.registerInt(name + "permutationSetsInvariant")),
      d_invariantByPermutationsTimer(
          sr.registerTimer(name + "timers::invariantByPermutations")),
      d_selectTermsTimer(sr.registerTimer(name + "timers::selectTerms")),
      d_initNormalizationTimer(
          sr.registerTimer(name + "timers::initNormalization"))
{
}

SymmetryBreaker::Terms::iterator
SymmetryBreaker::selectMostPromisingTerm(Terms& terms) {
  // use d_phi
  Trace("ufsymm") << "UFSYMM selectMostPromisingTerm()" << endl;
  return terms.begin();
}

void SymmetryBreaker::insertUsedIn(Term term, const Permutation& p, set<Node>& cts) {
  // insert terms from p used in term into cts
  //Trace("ufsymm") << "UFSYMM usedIn(): " << term << " , " << p << endl;
  if (p.find(term) != p.end()) {
    cts.insert(term);
  } else {
    for(TNode::iterator i = term.begin(); i != term.end(); ++i) {
      insertUsedIn(*i, p, cts);
    }
  }
}

}  // namespace uf
}  // namespace theory

std::ostream& operator<<(std::ostream& out, const theory::uf::SymmetryBreaker::Permutation& p) {
  out << "{";
  set<TNode>::const_iterator i = p.begin();
  while(i != p.end()) {
    out << *i;
    if(++i != p.end()) {
      out << ",";
    }
  }
  out << "}";
  return out;
}

}  // namespace cvc5::internal
