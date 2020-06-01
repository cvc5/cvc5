/*********************                                                        */
/*! \file base_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base solver for the theory of strings. This class implements term
 ** indexing and constant inference for the theory of strings.
 **/

#include "theory/strings/base_solver.h"

#include "options/strings_options.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

BaseSolver::BaseSolver(context::Context* c,
                       context::UserContext* u,
                       SolverState& s,
                       InferenceManager& im)
    : d_state(s), d_im(im), d_congruent(c)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_cardSize = utils::getAlphabetCardinality();
}

BaseSolver::~BaseSolver() {}

void BaseSolver::checkInit()
{
  // build term index
  d_eqcInfo.clear();
  d_termIndex.clear();
  d_stringsEqc.clear();

  std::map<Kind, uint32_t> ncongruent;
  std::map<Kind, uint32_t> congruent;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if (!tn.isRegExp())
    {
      Node emps;
      if (tn.isString())
      {
        d_stringsEqc.push_back(eqc);
        emps = Word::mkEmptyWord(tn);
      }
      Node var;
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
      while (!eqc_i.isFinished())
      {
        Node n = *eqc_i;
        if (n.isConst())
        {
          d_eqcInfo[eqc].d_bestContent = n;
          d_eqcInfo[eqc].d_base = n;
          d_eqcInfo[eqc].d_exp = Node::null();
        }
        else if (tn.isInteger())
        {
          // do nothing
        }
        else if (n.getNumChildren() > 0)
        {
          Kind k = n.getKind();
          if (k != EQUAL)
          {
            if (d_congruent.find(n) == d_congruent.end())
            {
              std::vector<Node> c;
              Node nc = d_termIndex[k].add(n, 0, d_state, emps, c);
              if (nc != n)
              {
                // check if we have inferred a new equality by removal of empty
                // components
                if (n.getKind() == STRING_CONCAT && !d_state.areEqual(nc, n))
                {
                  std::vector<Node> exp;
                  size_t count[2] = {0, 0};
                  while (count[0] < nc.getNumChildren()
                         || count[1] < n.getNumChildren())
                  {
                    // explain empty prefixes
                    for (unsigned t = 0; t < 2; t++)
                    {
                      Node nn = t == 0 ? nc : n;
                      while (count[t] < nn.getNumChildren()
                             && (nn[count[t]] == emps
                                 || d_state.areEqual(nn[count[t]], emps)))
                      {
                        if (nn[count[t]] != emps)
                        {
                          exp.push_back(nn[count[t]].eqNode(emps));
                        }
                        count[t]++;
                      }
                    }
                    // explain equal components
                    if (count[0] < nc.getNumChildren())
                    {
                      Assert(count[1] < n.getNumChildren());
                      if (nc[count[0]] != n[count[1]])
                      {
                        exp.push_back(nc[count[0]].eqNode(n[count[1]]));
                      }
                      count[0]++;
                      count[1]++;
                    }
                  }
                  // infer the equality
                  d_im.sendInference(exp, n.eqNode(nc), Inference::I_NORM);
                }
                else
                {
                  // We cannot mark one of the terms as reduced here (via
                  // ExtTheory::markCongruent) since extended function terms
                  // rely on reductions to other extended function terms. We
                  // may have a pair of extended function terms f(a)=f(b) where
                  // the reduction of argument a depends on the term b.
                  // Thus, marking f(b) as reduced by virtue of the fact we
                  // have f(a) is incorrect, since then we are effectively
                  // assuming that the reduction of f(a) depends on itself.
                }
                // this node is congruent to another one, we can ignore it
                Trace("strings-process-debug")
                    << "  congruent term : " << n << " (via " << nc << ")"
                    << std::endl;
                d_congruent.insert(n);
                congruent[k]++;
              }
              else if (k == STRING_CONCAT && c.size() == 1)
              {
                Trace("strings-process-debug")
                    << "  congruent term by singular : " << n << " " << c[0]
                    << std::endl;
                // singular case
                if (!d_state.areEqual(c[0], n))
                {
                  Node ns;
                  std::vector<Node> exp;
                  // explain empty components
                  bool foundNEmpty = false;
                  for (const Node& nnc : n)
                  {
                    if (d_state.areEqual(nnc, emps))
                    {
                      if (nnc != emps)
                      {
                        exp.push_back(nnc.eqNode(emps));
                      }
                    }
                    else
                    {
                      Assert(!foundNEmpty);
                      ns = nnc;
                      foundNEmpty = true;
                    }
                  }
                  AlwaysAssert(foundNEmpty);
                  // infer the equality
                  d_im.sendInference(exp, n.eqNode(ns), Inference::I_NORM_S);
                }
                d_congruent.insert(n);
                congruent[k]++;
              }
              else
              {
                ncongruent[k]++;
              }
            }
            else
            {
              congruent[k]++;
            }
          }
        }
        else
        {
          if (d_congruent.find(n) == d_congruent.end())
          {
            // We mark all but the oldest variable in the equivalence class as
            // congruent.
            if (var.isNull())
            {
              var = n;
            }
            else if (var > n)
            {
              Trace("strings-process-debug")
                  << "  congruent variable : " << var << std::endl;
              d_congruent.insert(var);
              var = n;
            }
            else
            {
              Trace("strings-process-debug")
                  << "  congruent variable : " << n << std::endl;
              d_congruent.insert(n);
            }
          }
        }
        ++eqc_i;
      }
    }
    ++eqcs_i;
  }
  if (Trace.isOn("strings-process"))
  {
    for (std::map<Kind, TermIndex>::iterator it = d_termIndex.begin();
         it != d_termIndex.end();
         ++it)
    {
      Trace("strings-process")
          << "  Terms[" << it->first << "] = " << ncongruent[it->first] << "/"
          << (congruent[it->first] + ncongruent[it->first]) << std::endl;
    }
  }
}

void BaseSolver::checkConstantEquivalenceClasses()
{
  // do fixed point
  size_t prevSize = 0;
  std::vector<Node> vecc;
  do
  {
    vecc.clear();
    Trace("strings-process-debug")
        << "Check constant equivalence classes..." << std::endl;
    prevSize = d_eqcInfo.size();
    checkConstantEquivalenceClasses(&d_termIndex[STRING_CONCAT], vecc, true);
  } while (!d_im.hasProcessed() && d_eqcInfo.size() > prevSize);

  if (!d_im.hasProcessed())
  {
    // now, go back and set "most content" terms
    vecc.clear();
    checkConstantEquivalenceClasses(&d_termIndex[STRING_CONCAT], vecc, false);
  }
}

void BaseSolver::checkConstantEquivalenceClasses(TermIndex* ti,
                                                 std::vector<Node>& vecc,
                                                 bool ensureConst,
                                                 bool isConst)
{
  Node n = ti->d_data;
  if (!n.isNull())
  {
    // construct the constant if applicable
    Node c;
    if (isConst)
    {
      c = utils::mkNConcat(vecc, n.getType());
    }
    if (!isConst || !d_state.areEqual(n, c))
    {
      if (Trace.isOn("strings-debug"))
      {
        Trace("strings-debug")
            << "Constant eqc : " << c << " for " << n << std::endl;
        Trace("strings-debug") << "  ";
        for (const Node& v : vecc)
        {
          Trace("strings-debug") << v << " ";
        }
        Trace("strings-debug") << std::endl;
      }
      size_t count = 0;
      size_t countc = 0;
      std::vector<Node> exp;
      // non-constant vector
      std::vector<Node> vecnc;
      size_t contentSize = 0;
      while (count < n.getNumChildren())
      {
        // Add explanations for the empty children
        Node emps;
        while (count < n.getNumChildren()
               && d_state.isEqualEmptyWord(n[count], emps))
        {
          d_im.addToExplanation(n[count], emps, exp);
          count++;
        }
        if (count < n.getNumChildren())
        {
          if (vecc[countc].isNull())
          {
            Assert(!isConst);
            // no constant for this component, leave it as is
            vecnc.push_back(n[count]);
          }
          else
          {
            if (!isConst)
            {
              // use the constant
              vecnc.push_back(vecc[countc]);
              Assert(vecc[countc].isConst());
              contentSize += Word::getLength(vecc[countc]);
            }
            Trace("strings-debug") << "...explain " << n[count] << " "
                                   << vecc[countc] << std::endl;
            if (!d_state.areEqual(n[count], vecc[countc]))
            {
              Node nrr = d_state.getRepresentative(n[count]);
              Assert(!d_eqcInfo[nrr].d_bestContent.isNull()
                     && d_eqcInfo[nrr].d_bestContent.isConst());
              d_im.addToExplanation(n[count], d_eqcInfo[nrr].d_base, exp);
              exp.push_back(d_eqcInfo[nrr].d_exp);
            }
            else
            {
              d_im.addToExplanation(n[count], vecc[countc], exp);
            }
            countc++;
          }
          count++;
        }
      }
      // exp contains an explanation of n==c
      Assert(!isConst || countc == vecc.size());
      if (!isConst)
      {
        // no use storing something with no content
        if (contentSize > 0)
        {
          Node nr = d_state.getRepresentative(n);
          BaseEqcInfo& bei = d_eqcInfo[nr];
          if (!bei.d_bestContent.isConst()
              && (bei.d_bestContent.isNull() || contentSize > bei.d_bestScore))
          {
            // The equivalence class is not entailed to be equal to a constant
            // and we found a better concatenation
            Node nct = utils::mkNConcat(vecnc, n.getType());
            Assert(!nct.isConst());
            bei.d_bestContent = nct;
            bei.d_base = n;
            bei.d_exp = utils::mkAnd(exp);
            Trace("strings-debug")
                << "Set eqc best content " << n << " to " << nct << std::endl;
          }
        }
      }
      else if (d_state.hasTerm(c))
      {
        d_im.sendInference(exp, n.eqNode(c), Inference::I_CONST_MERGE);
        return;
      }
      else if (!d_im.hasProcessed())
      {
        Node nr = d_state.getRepresentative(n);
        BaseEqcInfo& bei = d_eqcInfo[nr];
        if (!bei.d_bestContent.isConst())
        {
          Trace("strings-debug")
              << "Set eqc const " << n << " to " << c << std::endl;
          bei.d_bestContent = c;
          bei.d_base = n;
          bei.d_exp = utils::mkAnd(exp);
        }
        else if (c != bei.d_bestContent)
        {
          // conflict
          Trace("strings-debug")
              << "Conflict, other constant was " << bei.d_bestContent
              << ", this constant was " << c << std::endl;
          if (bei.d_exp.isNull())
          {
            // n==c ^ n == c' => false
            d_im.addToExplanation(n, bei.d_bestContent, exp);
          }
          else
          {
            // n==c ^ n == d_base == c' => false
            exp.push_back(bei.d_exp);
            d_im.addToExplanation(n, bei.d_base, exp);
          }
          d_im.sendInference(exp, d_false, Inference::I_CONST_CONFLICT);
          return;
        }
        else
        {
          Trace("strings-debug") << "Duplicate constant." << std::endl;
        }
      }
    }
  }
  for (std::pair<const TNode, TermIndex>& p : ti->d_children)
  {
    std::map<Node, BaseEqcInfo>::const_iterator it = d_eqcInfo.find(p.first);
    if (it != d_eqcInfo.end() && it->second.d_bestContent.isConst())
    {
      vecc.push_back(it->second.d_bestContent);
      checkConstantEquivalenceClasses(&p.second, vecc, ensureConst, isConst);
      vecc.pop_back();
    }
    else if (!ensureConst)
    {
      // can still proceed, with null
      vecc.push_back(Node::null());
      checkConstantEquivalenceClasses(&p.second, vecc, ensureConst, false);
      vecc.pop_back();
    }
    if (d_im.hasProcessed())
    {
      break;
    }
  }
}

void BaseSolver::checkCardinality()
{
  // This will create a partition of eqc, where each collection has length that
  // are pairwise propagated to be equal. We do not require disequalities
  // between the lengths of each collection, since we split on disequalities
  // between lengths of string terms that are disequal (DEQ-LENGTH-SP).
  std::vector<std::vector<Node> > cols;
  std::vector<Node> lts;
  d_state.separateByLength(d_stringsEqc, cols, lts);
  NodeManager* nm = NodeManager::currentNM();
  Trace("strings-card") << "Check cardinality...." << std::endl;
  // for each collection
  for (unsigned i = 0, csize = cols.size(); i < csize; ++i)
  {
    Node lr = lts[i];
    Trace("strings-card") << "Number of strings with length equal to " << lr
                          << " is " << cols[i].size() << std::endl;
    if (cols[i].size() <= 1)
    {
      // no restriction on sets in the partition of size 1
      continue;
    }
    // size > c^k
    unsigned card_need = 1;
    double curr = static_cast<double>(cols[i].size());
    while (curr > d_cardSize)
    {
      curr = curr / static_cast<double>(d_cardSize);
      card_need++;
    }
    Trace("strings-card")
        << "Need length " << card_need
        << " for this number of strings (where alphabet size is " << d_cardSize
        << ")." << std::endl;
    // check if we need to split
    bool needsSplit = true;
    if (lr.isConst())
    {
      // if constant, compare
      Node cmp = nm->mkNode(GEQ, lr, nm->mkConst(Rational(card_need)));
      cmp = Rewriter::rewrite(cmp);
      needsSplit = !cmp.getConst<bool>();
    }
    else
    {
      // find the minimimum constant that we are unknown to be disequal from, or
      // otherwise stop if we increment such that cardinality does not apply
      unsigned r = 0;
      bool success = true;
      while (r < card_need && success)
      {
        Node rr = nm->mkConst(Rational(r));
        if (d_state.areDisequal(rr, lr))
        {
          r++;
        }
        else
        {
          success = false;
        }
      }
      if (r > 0)
      {
        Trace("strings-card")
            << "Symbolic length " << lr << " must be at least " << r
            << " due to constant disequalities." << std::endl;
      }
      needsSplit = r < card_need;
    }

    if (!needsSplit)
    {
      // don't need to split
      continue;
    }
    // first, try to split to merge equivalence classes
    for (std::vector<Node>::iterator itr1 = cols[i].begin();
         itr1 != cols[i].end();
         ++itr1)
    {
      for (std::vector<Node>::iterator itr2 = itr1 + 1; itr2 != cols[i].end();
           ++itr2)
      {
        if (!d_state.areDisequal(*itr1, *itr2))
        {
          // add split lemma
          if (d_im.sendSplit(*itr1, *itr2, Inference::CARD_SP))
          {
            return;
          }
        }
      }
    }
    // otherwise, we need a length constraint
    uint32_t int_k = static_cast<uint32_t>(card_need);
    EqcInfo* ei = d_state.getOrMakeEqcInfo(lr, true);
    Trace("strings-card") << "Previous cardinality used for " << lr << " is "
                          << ((int)ei->d_cardinalityLemK.get() - 1)
                          << std::endl;
    if (int_k + 1 > ei->d_cardinalityLemK.get())
    {
      Node k_node = nm->mkConst(Rational(int_k));
      // add cardinality lemma
      Node dist = nm->mkNode(DISTINCT, cols[i]);
      std::vector<Node> vec_node;
      vec_node.push_back(dist);
      for (std::vector<Node>::iterator itr1 = cols[i].begin();
           itr1 != cols[i].end();
           ++itr1)
      {
        Node len = nm->mkNode(STRING_LENGTH, *itr1);
        if (len != lr)
        {
          Node len_eq_lr = len.eqNode(lr);
          vec_node.push_back(len_eq_lr);
        }
      }
      Node len = nm->mkNode(STRING_LENGTH, cols[i][0]);
      Node cons = nm->mkNode(GEQ, len, k_node);
      cons = Rewriter::rewrite(cons);
      ei->d_cardinalityLemK.set(int_k + 1);
      if (!cons.isConst() || !cons.getConst<bool>())
      {
        std::vector<Node> emptyVec;
        d_im.sendInference(
            emptyVec, vec_node, cons, Inference::CARDINALITY, true);
        return;
      }
    }
  }
  Trace("strings-card") << "...end check cardinality" << std::endl;
}

bool BaseSolver::isCongruent(Node n)
{
  return d_congruent.find(n) != d_congruent.end();
}

Node BaseSolver::getConstantEqc(Node eqc)
{
  std::map<Node, BaseEqcInfo>::const_iterator it = d_eqcInfo.find(eqc);
  if (it != d_eqcInfo.end() && it->second.d_bestContent.isConst())
  {
    return it->second.d_bestContent;
  }
  return Node::null();
}

Node BaseSolver::explainConstantEqc(Node n, Node eqc, std::vector<Node>& exp)
{
  std::map<Node, BaseEqcInfo>::const_iterator it = d_eqcInfo.find(eqc);
  if (it != d_eqcInfo.end())
  {
    BaseEqcInfo& bei = d_eqcInfo[eqc];
    if (!bei.d_bestContent.isConst())
    {
      return Node::null();
    }
    if (!bei.d_exp.isNull())
    {
      exp.push_back(bei.d_exp);
    }
    if (!bei.d_base.isNull())
    {
      d_im.addToExplanation(n, bei.d_base, exp);
    }
    return bei.d_bestContent;
  }
  return Node::null();
}

Node BaseSolver::explainBestContentEqc(Node n, Node eqc, std::vector<Node>& exp)
{
  std::map<Node, BaseEqcInfo>::const_iterator it = d_eqcInfo.find(eqc);
  if (it != d_eqcInfo.end())
  {
    BaseEqcInfo& bei = d_eqcInfo[eqc];
    Assert(!bei.d_bestContent.isNull());
    if (!bei.d_exp.isNull())
    {
      exp.push_back(bei.d_exp);
    }
    if (!bei.d_base.isNull())
    {
      d_im.addToExplanation(n, bei.d_base, exp);
    }
    return bei.d_bestContent;
  }

  return Node::null();
}

const std::vector<Node>& BaseSolver::getStringEqc() const
{
  return d_stringsEqc;
}

Node BaseSolver::TermIndex::add(TNode n,
                                unsigned index,
                                const SolverState& s,
                                Node er,
                                std::vector<Node>& c)
{
  if (index == n.getNumChildren())
  {
    if (d_data.isNull())
    {
      d_data = n;
    }
    return d_data;
  }
  Assert(index < n.getNumChildren());
  TNode nir = s.getRepresentative(n[index]);
  // if it is empty, and doing CONCAT, ignore
  if (nir == er && n.getKind() == STRING_CONCAT)
  {
    return add(n, index + 1, s, er, c);
  }
  c.push_back(nir);
  return d_children[nir].add(n, index + 1, s, er, c);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
