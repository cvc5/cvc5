/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base solver for the theory of strings. This class implements term
 * indexing and constant inference for the theory of strings.
 */

#include "theory/strings/base_solver.h"

#include "expr/sequence.h"
#include "options/quantifiers_options.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/string.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

BaseSolver::BaseSolver(Env& env,
                       SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_congruent(context()),
      d_strUnitOobEq(userContext())
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_cardSize = options().strings.stringsAlphaCard;
}

BaseSolver::~BaseSolver() {}

void BaseSolver::checkInit()
{
  // build term index
  d_eqcInfo.clear();
  d_termIndex.clear();
  d_stringLikeEqc.clear();

  const std::set<Node>& rlvSet = d_termReg.getRelevantTermSet();

  Trace("strings-base") << "BaseSolver::checkInit" << std::endl;
  // count of congruent, non-congruent per operator (independent of type),
  // for debugging.
  std::map<Kind, std::pair<uint32_t, uint32_t>> congruentCount;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if (!tn.isRegExp())
    {
      Node emps;
      // get the term index for type tn
      std::map<Kind, TermIndex>& tti = d_termIndex[tn];
      if (tn.isStringLike())
      {
        d_stringLikeEqc.push_back(eqc);
        emps = Word::mkEmptyWord(tn);
      }
      Node var;
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
      std::vector<Node> prevConstLike;
      bool isString = eqc.getType().isString();
      // have we found a constant in this equivalence class
      bool foundConst = false;
      for (; !eqc_i.isFinished(); ++eqc_i)
      {
        Node n = *eqc_i;
        Kind k = n.getKind();
        Trace("strings-base") << "initialize term: " << n << std::endl;
        // process constant-like terms
        if (utils::isConstantLike(n))
        {
          // compare against the other constant-like terms in this equivalence
          // class
          for (const Node& prev : prevConstLike)
          {
            if (processConstantLike(n, prev))
            {
              // in conflict, return
              return;
            }
          }
          bool addToConstLike = isString && !foundConst;
          // update best content
          if (prevConstLike.empty() || n.isConst())
          {
            d_eqcInfo[eqc].d_bestContent = n;
            d_eqcInfo[eqc].d_bestScore = 0;
            d_eqcInfo[eqc].d_base = n;
            d_eqcInfo[eqc].d_exp = Node::null();
            if (n.isConst())
            {
              // only keep the current
              prevConstLike.clear();
              foundConst = true;
            }
          }
          // Determine if we need to track n to compare it to other constant
          // like terms in this equivalence class. This is done if we do not
          // have any other constant-like terms we are tracking, or if we have
          // not yet encountered a constant and we are a string equivalence
          // class. This is because all *pairs* of str.unit must be compared
          // to one another, whereas since seq.unit is injective, we can
          // compare seq.unit with a single representative seq.unit term.
          if (prevConstLike.empty() || addToConstLike)
          {
            prevConstLike.push_back(n);
          }
        }

        if (tn.isInteger())
        {
          // do nothing
          continue;
        }
        else if (d_congruent.find(n) != d_congruent.end())
        {
          // skip congruent terms
          congruentCount[k].first++;
          continue;
        }

        congruentCount[k].second++;

        // process indexing
        if (n.getNumChildren() > 0)
        {
          if (k == EQUAL)
          {
            continue;
          }

          std::vector<Node> c;
          Node nc = tti[k].add(n, 0, d_state, emps, false, c);
          if (nc != n)
          {
            Trace("strings-base-debug")
                << "...found congruent term " << nc << std::endl;
            // check if we have inferred a new equality by removal of empty
            // components
            if (k == STRING_CONCAT && !d_state.areEqual(nc, n))
            {
              std::vector<Node> exp;
              // the number of empty components of n, nc
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
                Trace("strings-base-debug") << "  counts = " << count[0] << ", "
                                            << count[1] << std::endl;
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
              d_im.sendInference(
                  exp, n.eqNode(nc), InferenceId::STRINGS_I_NORM);
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
            if (rlvSet.find(n) != rlvSet.end()
                && rlvSet.find(nc) == rlvSet.end())
            {
              // If `n` is a relevant term and `nc` is not, then we change
              // the term at its index to `n` and mark `nc` as congruent.
              // This ensures that if we have mutliple congruent terms, we
              // reason about one of the relevant ones (if available).
              tti[k].add(n, 0, d_state, emps, true, c);
              std::swap(nc, n);
            }
            Trace("strings-base-debug")
                << "  congruent term : " << n << " (via " << nc << ")"
                << std::endl;
            d_congruent.insert(n);
            congruentCount[k].first++;
          }
          else if (k == STRING_CONCAT && c.size() == 1)
          {
            Trace("strings-base-debug")
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
              d_im.sendInference(
                  exp, n.eqNode(ns), InferenceId::STRINGS_I_NORM_S);
            }
            d_congruent.insert(n);
          }
        }
        else if (!n.isConst())
        {
          // We mark all but the oldest variable in the equivalence class as
          // congruent.
          if (var.isNull())
          {
            var = n;
          }
          else if (var > n)
          {
            Trace("strings-base-debug")
                << "  congruent variable : " << var << std::endl;
            d_congruent.insert(var);
            var = n;
          }
          else
          {
            Trace("strings-base-debug")
                << "  congruent variable : " << n << std::endl;
            d_congruent.insert(n);
          }
        }
      }
    }
    ++eqcs_i;
  }
  if (TraceIsOn("strings-base"))
  {
    for (const std::pair<const Kind, std::pair<uint32_t, uint32_t>>& cc :
         congruentCount)
    {
      Trace("strings-base")
          << "  Terms[" << cc.first << "] = " << cc.second.second << "/"
          << (cc.second.first + cc.second.second) << std::endl;
    }
  }
  Trace("strings-base") << "BaseSolver::checkInit finished" << std::endl;
}

bool BaseSolver::processConstantLike(Node a, Node b)
{
  // we have either (seq.unit x) = C, or (seq.unit x) = (seq.unit y)
  // where C is a sequence constant.
  Node cval = b.isConst() ? b : (a.isConst() ? a : Node::null());
  std::vector<Node> exp;
  exp.push_back(b.eqNode(a));
  Node s, t;
  if (cval.isNull())
  {
    // injectivity of seq.unit
    s = b[0];
    t = a[0];
  }
  else
  {
    // should not have two constants in the same equivalence class
    std::vector<Node> cchars = Word::getChars(cval);
    if (cchars.size() == 1)
    {
      Node oval = b.isConst() ? a : b;
      Assert(oval.getKind() == SEQ_UNIT || oval.getKind() == STRING_UNIT);
      s = oval[0];
      t = Word::getNth(cchars[0], 0);
      // oval is congruent (ignored) in this context
      d_congruent.insert(oval);
    }
    else
    {
      // (seq.unit x) = C => false if |C| != 1.
      d_im.sendInference(
          exp, d_false, InferenceId::STRINGS_UNIT_CONST_CONFLICT);
      return true;
    }
  }
  Trace("strings-base") << "Process constant-like pair " << s << ", " << t
                        << " from " << a << ", " << b << std::endl;
  if (!d_state.areEqual(s, t))
  {
    Assert(s.getType() == t.getType());
    Node eq = s.eqNode(t);
    if (a.getType().isString())
    {
      // String unit is not injective, due to invalid code points.
      // We do an inference scheme in two parts.
      // for (str.unit x), (str.unit y): x = y or x != y
      if (!d_state.areDisequal(s, t))
      {
        d_im.sendSplit(s, t, InferenceId::STRINGS_UNIT_SPLIT);
        Trace("strings-base") << "...split" << std::endl;
      }
      else if (d_strUnitOobEq.find(eq) == d_strUnitOobEq.end())
      {
        // cache that we have performed this inference
        Node eqSym = t.eqNode(s);
        d_strUnitOobEq.insert(eq);
        d_strUnitOobEq.insert(eqSym);
        exp.push_back(eq.notNode());
        // (str.unit x) = (str.unit y) ^ x != y =>
        // x or y is not a valid code point
        Node scr = utils::mkCodeRange(s, d_cardSize);
        Node tcr = utils::mkCodeRange(t, d_cardSize);
        Node conc =
            NodeManager::currentNM()->mkNode(OR, scr.notNode(), tcr.notNode());
        // We do not explain exp for two reasons. First, we are
        // caching this inference based on the user context and thus
        // it should not depend on the current explanation. Second,
        // s or t may be concrete integers corresponding to code
        // points of string constants, and thus are not guaranteed to
        // be terms in the equality engine.
        NodeManager* nm = NodeManager::currentNM();
        // We must send this lemma immediately, since otherwise if buffered,
        // this lemma may be dropped if there is a fact or conflict that
        // preempts it.
        Node lem = nm->mkNode(IMPLIES, nm->mkAnd(exp), conc);
        d_im.lemma(lem, InferenceId::STRINGS_UNIT_INJ_OOB);
        Trace("strings-base") << "...oob split" << std::endl;
      }
      else
      {
        Trace("strings-base") << "...already sent oob" << std::endl;
      }
    }
    else
    {
      // (seq.unit x) = (seq.unit y) => x=y, or
      // (seq.unit x) = (seq.unit c) => x=c
      // Must send this as lemma since it may impact other theories, or
      // imply length constraints if the conclusion involves strings/sequences.
      d_im.sendInference(exp, eq, InferenceId::STRINGS_UNIT_INJ, false, true);
      Trace("strings-base") << "...inj seq" << std::endl;
    }
  }
  else
  {
    Trace("strings-base") << "...equal" << std::endl;
  }
  return false;
}

void BaseSolver::checkConstantEquivalenceClasses()
{
  // do fixed point
  size_t prevSize = 0;
  std::vector<Node> vecc;
  do
  {
    vecc.clear();
    Trace("strings-base-debug")
        << "Check constant equivalence classes..." << std::endl;
    prevSize = d_eqcInfo.size();
    for (std::pair<const TypeNode, std::map<Kind, TermIndex>>& tindex :
         d_termIndex)
    {
      checkConstantEquivalenceClasses(
          &tindex.second[STRING_CONCAT], vecc, true);
    }
  } while (!d_im.hasProcessed() && d_eqcInfo.size() > prevSize);

  if (!d_im.hasProcessed())
  {
    // now, go back and set "most content" terms
    vecc.clear();
    for (std::pair<const TypeNode, std::map<Kind, TermIndex>>& tindex :
         d_termIndex)
    {
      checkConstantEquivalenceClasses(
          &tindex.second[STRING_CONCAT], vecc, false);
    }
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
      c = d_termReg.mkNConcat(vecc, n.getType());
    }
    if (!isConst || !d_state.areEqual(n, c))
    {
      if (TraceIsOn("strings-debug"))
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
      size_t countc = 0;
      std::vector<Node> exp;
      // non-constant vector
      std::vector<Node> vecnc;
      size_t contentSize = 0;
      for (size_t count = 0, nchild = n.getNumChildren(); count < nchild;
           ++count)
      {
        // Add explanations for the empty children
        Node emps;
        if (d_state.isEqualEmptyWord(n[count], emps))
        {
          d_im.addToExplanation(n[count], emps, exp);
          continue;
        }
        else if (vecc[countc].isNull())
        {
          Assert(!isConst);
          // no constant for this component, leave it as is
          vecnc.push_back(n[count]);
          continue;
        }
        // if we are not entirely a constant
        if (!isConst)
        {
          // use the constant component
          vecnc.push_back(vecc[countc]);
          Assert(vecc[countc].isConst());
          contentSize += Word::getLength(vecc[countc]);
        }
        Trace("strings-debug")
            << "...explain " << n[count] << " " << vecc[countc] << std::endl;
        if (!d_state.areEqual(n[count], vecc[countc]))
        {
          Node nrr = d_state.getRepresentative(n[count]);
          Assert(!d_eqcInfo[nrr].d_bestContent.isNull()
                 && d_eqcInfo[nrr].d_bestContent.isConst());
          // must flatten to avoid nested AND in explanations
          utils::flattenOp(AND, d_eqcInfo[nrr].d_exp, exp);
          // now explain equality to base
          d_im.addToExplanation(n[count], d_eqcInfo[nrr].d_base, exp);
        }
        else
        {
          d_im.addToExplanation(n[count], vecc[countc], exp);
        }
        countc++;
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
            Node nct = d_termReg.mkNConcat(vecnc, n.getType());
            Assert(!nct.isConst());
            bei.d_bestContent = nct;
            bei.d_bestScore = contentSize;
            bei.d_base = n;
            if (!exp.empty())
            {
              bei.d_exp = utils::mkAnd(exp);
            }
            Trace("strings-debug")
                << "Set eqc best content " << n << " to " << nct
                << ", explanation = " << bei.d_exp << std::endl;
          }
        }
      }
      else if (d_state.hasTerm(c))
      {
        d_im.sendInference(exp, n.eqNode(c), InferenceId::STRINGS_I_CONST_MERGE);
        return;
      }
      else if (!d_im.hasProcessed())
      {
        Node nr = d_state.getRepresentative(n);
        BaseEqcInfo& bei = d_eqcInfo[nr];
        if (!bei.d_bestContent.isConst())
        {
          bei.d_bestContent = c;
          bei.d_base = n;
          bei.d_exp = utils::mkAnd(exp);
          Trace("strings-debug")
              << "Set eqc const " << n << " to " << c
              << ", explanation = " << bei.d_exp << std::endl;
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
          d_im.sendInference(exp, d_false, InferenceId::STRINGS_I_CONST_CONFLICT);
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
  std::map<TypeNode, std::vector<std::vector<Node> > > cols;
  std::map<TypeNode, std::vector<Node> > lts;
  d_state.separateByLengthTyped(d_stringLikeEqc, cols, lts);
  for (std::pair<const TypeNode, std::vector<std::vector<Node> > >& c : cols)
  {
    checkCardinalityType(c.first, c.second, lts[c.first]);
  }
}

BaseSolver::CardinalityResponse BaseSolver::getCardinalityReq(
    TypeNode tn, size_t& typeCardSize) const
{
  if (tn.isString())  // string-only
  {
    typeCardSize = d_cardSize;
    return CardinalityResponse::REQ;
  }
  Assert(tn.isSequence());
  TypeNode etn = tn.getSequenceElementType();
  if (!d_env.isFiniteType(etn))
  {
    // infinite cardinality, we are fine
    return CardinalityResponse::NO_REQ;
  }
  // we check the cardinality class of the type, assuming that FMF is
  // disabled.
  if (isCardinalityClassFinite(etn.getCardinalityClass(), false))
  {
    Cardinality c = etn.getCardinality();
    bool smallCardinality = false;
    if (!c.isLargeFinite())
    {
      Integer ci = c.getFiniteCardinality();
      if (ci.fitsUnsignedInt())
      {
        smallCardinality = true;
        typeCardSize = ci.toUnsignedInt();
      }
    }
    if (!smallCardinality)
    {
      // if it is large finite, then there is no way we could have
      // constructed that many terms in memory, hence there is nothing
      // to do.
      return CardinalityResponse::NO_REQ;
    }
  }
  else
  {
    Assert(options().quantifiers.finiteModelFind);
    // we are in a case where the cardinality of the type is infinite
    // if not FMF, and finite given the Env's option value for FMF. In this
    // case, FMF must be true, and the cardinality is finite and dynamic
    // (i.e. it depends on the model's finite interpretation for uninterpreted
    // sorts). We do not know how to handle this case, we set incomplete.
    // TODO (cvc4-projects #23): how to handle sequence for finite types?
    d_im.setModelUnsound(IncompleteId::SEQ_FINITE_DYNAMIC_CARDINALITY);
    return CardinalityResponse::UNHANDLED;
  }
  return CardinalityResponse::REQ;
}

bool BaseSolver::isCardinalityOk(size_t typeCardSize,
                                 Node lr,
                                 size_t eqcCount,
                                 size_t& lenNeed) const
{
  Trace("strings-card") << "isCardinalityOk? " << typeCardSize << " "
                        << eqcCount << std::endl;
  if (eqcCount <= 1)
  {
    return true;
  }
  else if (typeCardSize == 1)
  {
    return false;
  }
  lenNeed = 1;
  double curr = static_cast<double>(eqcCount);
  while (curr > typeCardSize)
  {
    curr = curr / static_cast<double>(typeCardSize);
    lenNeed++;
  }
  Trace("strings-card")
      << "Need length " << lenNeed
      << " for this number of strings (where alphabet size is " << typeCardSize
      << ")." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // check if we need to split
  bool needsSplit = true;
  if (lr.isConst())
  {
    // if constant, compare
    Node cmp = nm->mkNode(GEQ, lr, nm->mkConstInt(Rational(lenNeed)));
    cmp = rewrite(cmp);
    needsSplit = !cmp.getConst<bool>();
  }
  else
  {
    // find the minimimum constant that we are unknown to be disequal from, or
    // otherwise stop if we increment such that cardinality does not apply.
    // We always start with r=1 since by the invariants of our term registry,
    // a term is either equal to the empty string, or has length >= 1.
    size_t r = 1;
    bool success = true;
    while (r < lenNeed && success)
    {
      Node rr = nm->mkConstInt(Rational(r));
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
    needsSplit = r < lenNeed;
  }
  return !needsSplit;
}
bool BaseSolver::isCardinalityOk(size_t typeCardSize,
                                 Node lr,
                                 size_t eqcCount) const
{
  size_t lenNeed;
  return isCardinalityOk(typeCardSize, lr, eqcCount, lenNeed);
}

void BaseSolver::checkCardinalityType(TypeNode tn,
                                      std::vector<std::vector<Node>>& cols,
                                      std::vector<Node>& lts)
{
  Trace("strings-card") << "Check cardinality (type " << tn << ")..."
                        << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  size_t typeCardSize;
  CardinalityResponse cr = getCardinalityReq(tn, typeCardSize);
  if (cr == CardinalityResponse::NO_REQ)
  {
    // no requirements, return
    return;
  }
  else if (cr == CardinalityResponse::UNHANDLED)
  {
    // we are in a case where the cardinality of the type is infinite
    // if not FMF, and finite given the Env's option value for FMF. In this
    // case, FMF must be true, and the cardinality is finite and dynamic
    // (i.e. it depends on the model's finite interpretation for uninterpreted
    // sorts). We do not know how to handle this case, we set incomplete.
    // TODO (cvc4-projects #23): how to handle sequence for finite types?
    d_im.setModelUnsound(IncompleteId::SEQ_FINITE_DYNAMIC_CARDINALITY);
    return;
  }
  // for each collection
  for (unsigned i = 0, csize = cols.size(); i < csize; ++i)
  {
    Node lr = lts[i];
    Trace("strings-card") << "Number of strings with length equal to " << lr
                          << " is " << cols[i].size() << std::endl;
    size_t lenNeed;
    if (isCardinalityOk(typeCardSize, lr, cols[i].size(), lenNeed))
    {
      // based on cardinality, we are ok
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
          if (d_im.sendSplit(*itr1, *itr2, InferenceId::STRINGS_CARD_SP))
          {
            return;
          }
        }
      }
    }
    // otherwise, we need a length constraint
    EqcInfo* ei = d_state.getOrMakeEqcInfo(lr, true);
    Trace("strings-card") << "Previous cardinality used for " << lr << " is "
                          << ((int)ei->d_cardinalityLemK.get() - 1)
                          << std::endl;
    if (lenNeed + 1 > ei->d_cardinalityLemK.get())
    {
      Node k_node = nm->mkConstInt(Rational(lenNeed));
      // add cardinality lemma
      Node dist = nm->mkNode(DISTINCT, cols[i]);
      std::vector<Node> expn;
      expn.push_back(dist);
      for (std::vector<Node>::iterator itr1 = cols[i].begin();
           itr1 != cols[i].end();
           ++itr1)
      {
        Node len = nm->mkNode(STRING_LENGTH, *itr1);
        if (len != lr)
        {
          Node len_eq_lr = len.eqNode(lr);
          expn.push_back(len_eq_lr);
        }
      }
      Node len = nm->mkNode(STRING_LENGTH, cols[i][0]);
      Node cons = nm->mkNode(GEQ, len, k_node);
      cons = rewrite(cons);
      ei->d_cardinalityLemK.set(lenNeed + 1);
      if (!cons.isConst() || !cons.getConst<bool>())
      {
        d_im.sendInference(
            expn, expn, cons, InferenceId::STRINGS_CARDINALITY, false, true);
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
      utils::flattenOp(AND, bei.d_exp, exp);
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
      utils::flattenOp(AND, bei.d_exp, exp);
    }
    if (!bei.d_base.isNull())
    {
      d_im.addToExplanation(n, bei.d_base, exp);
    }
    return bei.d_bestContent;
  }

  return Node::null();
}

const std::vector<Node>& BaseSolver::getStringLikeEqc() const
{
  return d_stringLikeEqc;
}

Node BaseSolver::TermIndex::add(TNode n,
                                unsigned index,
                                const SolverState& s,
                                Node er,
                                bool overwrite,
                                std::vector<Node>& c)
{
  if (index == n.getNumChildren())
  {
    if (overwrite || d_data.isNull())
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
    return add(n, index + 1, s, er, overwrite, c);
  }
  c.push_back(nir);
  return d_children[nir].add(n, index + 1, s, er, overwrite, c);
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
