/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model object for the non-linear extension class.
 */

#include "theory/arith/nl/nl_model.h"

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/theory_model.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

NlModel::NlModel(Env& env) : EnvObj(env), d_used_approx(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConstReal(Rational(0));
  d_one = NodeManager::currentNM()->mkConstReal(Rational(1));
  d_two = NodeManager::currentNM()->mkConstReal(Rational(2));
}

NlModel::~NlModel() {}

void NlModel::reset(const std::map<Node, Node>& arithModel)
{
  d_concreteModelCache.clear();
  d_abstractModelCache.clear();
  d_arithVal = arithModel;
}

void NlModel::resetCheck()
{
  d_used_approx = false;
  d_check_model_solved.clear();
  d_check_model_bounds.clear();
  d_substitutions.clear();
}

Node NlModel::computeConcreteModelValue(TNode n)
{
  return computeModelValue(n, true);
}

Node NlModel::computeAbstractModelValue(TNode n)
{
  return computeModelValue(n, false);
}

Node NlModel::computeModelValue(TNode n, bool isConcrete)
{
  auto& cache = isConcrete ? d_concreteModelCache : d_abstractModelCache;
  if (auto it = cache.find(n); it != cache.end())
  {
    return it->second;
  }
  Trace("nl-ext-mv-debug") << "computeModelValue " << n
                           << ", isConcrete=" << isConcrete << std::endl;
  Node ret;
  if (n.isConst())
  {
    ret = n;
  }
  else if (!isConcrete && hasLinearModelValue(n, ret))
  {
    // use model value for abstraction
  }
  else if (n.getNumChildren() == 0)
  {
    // we are interested in the exact value of PI, which cannot be computed.
    // hence, we return PI itself when asked for the concrete value.
    if (n.getKind() == PI)
    {
      ret = n;
    }
    else
    {
      ret = getValueInternal(n);
    }
  }
  else
  {
    // otherwise, compute true value
    TheoryId ctid = theory::kindToTheoryId(n.getKind());
    if (ctid != THEORY_ARITH && ctid != THEORY_BOOL && ctid != THEORY_BUILTIN)
    {
      // we directly look up terms not belonging to arithmetic
      ret = getValueInternal(n);
    }
    else
    {
      std::vector<Node> children;
      if (n.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.emplace_back(n.getOperator());
      }
      for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        children.emplace_back(computeModelValue(n[i], isConcrete));
      }
      ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
      ret = rewrite(ret);
    }
  }
  Trace("nl-ext-mv-debug") << "computed " << (isConcrete ? "M" : "M_A") << "["
                           << n << "] = " << ret << std::endl;
  Assert(n.getType() == ret.getType());
  cache[n] = ret;
  return ret;
}

int NlModel::compare(TNode i, TNode j, bool isConcrete, bool isAbsolute)
{
  if (i == j)
  {
    return 0;
  }
  Node ci = computeModelValue(i, isConcrete);
  Node cj = computeModelValue(j, isConcrete);
  if (ci.isConst())
  {
    if (cj.isConst())
    {
      return compareValue(ci, cj, isAbsolute);
    }
    return 1;
  }
  return cj.isConst() ? -1 : 0;
}

int NlModel::compareValue(TNode i, TNode j, bool isAbsolute) const
{
  Assert(i.isConst() && j.isConst());
  if (i == j)
  {
    return 0;
  }
  if (!isAbsolute)
  {
    return i.getConst<Rational>() < j.getConst<Rational>() ? -1 : 1;
  }
  Rational iabs = i.getConst<Rational>().abs();
  Rational jabs = j.getConst<Rational>().abs();
  if (iabs == jabs)
  {
    return 0;
  }
  return iabs < jabs ? -1 : 1;
}

bool NlModel::checkModel(const std::vector<Node>& assertions,
                         unsigned d,
                         std::vector<NlLemma>& lemmas)
{
  Trace("nl-ext-cm-debug") << "NlModel::checkModel: solve for equalities..."
                           << std::endl;
  for (const Node& atom : assertions)
  {
    Trace("nl-ext-cm-debug") << "- assertion: " << atom << std::endl;
    // see if it corresponds to a univariate polynomial equation of degree two
    if (atom.getKind() == EQUAL)
    {
      // we substitute inside of solve equality simple
      if (!solveEqualitySimple(atom, d, lemmas))
      {
        // no chance we will satisfy this equality
        Trace("nl-ext-cm") << "...check-model : failed to solve equality : "
                           << atom << std::endl;
      }
    }
  }

  // all remaining variables are constrained to their exact model values
  Trace("nl-ext-cm-debug") << "  set exact bounds for remaining variables..."
                           << std::endl;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  for (const Node& a : assertions)
  {
    visit.push_back(a);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end())
      {
        visited.insert(cur);
        if (cur.getType().isRealOrInt() && !cur.isConst())
        {
          Kind k = cur.getKind();
          if (k != MULT && k != ADD && k != NONLINEAR_MULT && k != TO_REAL
              && !isTranscendentalKind(k) && k != IAND && k != POW2)
          {
            // if we have not set an approximate bound for it
            if (!hasAssignment(cur))
            {
              // set its exact model value in the substitution, if we compute
              // a constant value
              Node curv = computeConcreteModelValue(cur);
              if (curv.isConst())
              {
                if (TraceIsOn("nl-ext-cm"))
                {
                  Trace("nl-ext-cm")
                      << "check-model-bound : exact : " << cur << " = ";
                  printRationalApprox("nl-ext-cm", curv);
                  Trace("nl-ext-cm") << std::endl;
                }
                bool ret = addSubstitution(cur, curv);
                AlwaysAssert(ret);
              }
            }
          }
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    } while (!visit.empty());
  }

  Trace("nl-ext-cm-debug") << "  check assertions..." << std::endl;
  std::vector<Node> check_assertions;
  for (const Node& a : assertions)
  {
    if (d_check_model_solved.find(a) == d_check_model_solved.end())
    {
      // apply the substitution to a
      Node av = getSubstitutedForm(a);
      Trace("nl-ext-cm") << "simpleCheckModelLit " << av << " (from " << a
                         << ")" << std::endl;
      // simple check literal
      if (!simpleCheckModelLit(av))
      {
        Trace("nl-ext-cm") << "...check-model : assertion failed : " << a
                           << std::endl;
        check_assertions.push_back(av);
        Trace("nl-ext-cm-debug")
            << "...check-model : failed assertion, value : " << av << std::endl;
      }
    }
  }

  if (!check_assertions.empty())
  {
    Trace("nl-ext-cm") << "...simple check failed." << std::endl;
    // TODO (#1450) check model for general case
    return false;
  }
  Trace("nl-ext-cm") << "...simple check succeeded!" << std::endl;
  return true;
}

bool NlModel::addSubstitution(TNode v, TNode s)
{
  Assert(v.getKind() != TO_REAL);
  Trace("nl-ext-model") << "* check model substitution : " << v << " -> " << s
                        << std::endl;
  Assert(getSubstitutedForm(s) == s)
      << "Added a substitution whose range is not in substituted form " << s;
  // cannot substitute real for integer
  Assert(v.getType().isReal() || s.getType().isInteger());
  // should not substitute the same variable twice
  // should not set exact bound more than once
  if (d_substitutions.contains(v))
  {
    Node cur = d_substitutions.getSubs(v);
    if (cur != s)
    {
      Trace("nl-ext-model")
          << "...warning: already has value: " << cur << std::endl;
      // We set two different substitutions for a variable v. If both are
      // constant, then we throw an error. Otherwise, we ignore the newer
      // substitution and return false here.
      Assert(!cur.isConst() || !s.isConst())
          << "Conflicting exact bounds given for a variable (" << cur << " and "
          << s << ") for " << v;
      return false;
    }
  }
  // if we previously had an approximate bound, the exact bound should be in its
  // range
  std::map<Node, std::pair<Node, Node>>::iterator itb =
      d_check_model_bounds.find(v);
  if (itb != d_check_model_bounds.end())
  {
    Assert(s.isConst());
    if (s.getConst<Rational>() <= itb->second.first.getConst<Rational>()
        || s.getConst<Rational>() >= itb->second.second.getConst<Rational>())
    {
      Trace("nl-ext-model")
          << "...ERROR: already has bound which is out of range." << std::endl;
      Assert(false) << "Out of bounds exact bound given for a variable with an "
                       "approximate bound";
      return false;
    }
  }
  ArithSubs tmp;
  tmp.addArith(v, s);
  for (auto& sub : d_substitutions.d_subs)
  {
    Node ms = tmp.applyArith(sub);
    if (ms != sub)
    {
      sub = rewrite(ms);
    }
  }
  d_substitutions.addArith(v, s);
  return true;
}

bool NlModel::addBound(TNode v, TNode l, TNode u)
{
  Assert(l.getType() == v.getType());
  Assert(u.getType() == v.getType());
  Trace("nl-ext-model") << "* check model bound : " << v << " -> [" << l << " "
                        << u << "]" << std::endl;
  if (l == u)
  {
    // bound is exact, can add as substitution
    return addSubstitution(v, l);
  }
  // should not set a bound for a value that is exact
  if (d_substitutions.contains(v))
  {
    Trace("nl-ext-model")
        << "...ERROR: setting bound for variable that already has exact value."
        << std::endl;
    Assert(false) << "Setting bound for variable that already has exact value.";
    return false;
  }
  Assert(l.isConst());
  Assert(u.isConst());
  Assert(l.getConst<Rational>() <= u.getConst<Rational>());
  d_check_model_bounds[v] = std::pair<Node, Node>(l, u);
  if (TraceIsOn("nl-ext-cm"))
  {
    Trace("nl-ext-cm") << "check-model-bound : approximate : ";
    printRationalApprox("nl-ext-cm", l);
    Trace("nl-ext-cm") << " <= " << v << " <= ";
    printRationalApprox("nl-ext-cm", u);
    Trace("nl-ext-cm") << std::endl;
  }
  return true;
}

void NlModel::setUsedApproximate() { d_used_approx = true; }

bool NlModel::usedApproximate() const { return d_used_approx; }

bool NlModel::solveEqualitySimple(Node eq,
                                  unsigned d,
                                  std::vector<NlLemma>& lemmas)
{
  Node seq = eq;
  if (!d_substitutions.empty())
  {
    seq = getSubstitutedForm(eq);
    if (seq.isConst())
    {
      if (seq.getConst<bool>())
      {
        // already true
        d_check_model_solved[eq] = Node::null();
        return true;
      }
      return false;
    }
  }
  Trace("nl-ext-cms") << "simple solve equality " << seq << "..." << std::endl;
  Assert(seq.getKind() == EQUAL);
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(seq, msum))
  {
    Trace("nl-ext-cms") << "...fail, could not determine monomial sum."
                        << std::endl;
    return false;
  }
  bool is_valid = true;
  // the variable we will solve a quadratic equation for
  Node var;
  Node b = d_zero;
  Node c = d_zero;
  NodeManager* nm = NodeManager::currentNM();
  // the list of variables that occur as a monomial in msum, and whose value
  // is so far unconstrained in the model.
  std::unordered_set<Node> unc_vars;
  // the list of variables that occur as a factor in a monomial, and whose
  // value is so far unconstrained in the model.
  std::unordered_set<Node> unc_vars_factor;
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    Node coeff = m.second.isNull() ? d_one : m.second;
    if (v.isNull())
    {
      c = coeff;
    }
    else if (v.getKind() == NONLINEAR_MULT)
    {
      is_valid = false;
      Trace("nl-ext-cms-debug")
          << "...invalid due to non-linear monomial " << v << std::endl;
      // may wish to set an exact bound for a factor and repeat
      for (const Node& vc : v)
      {
        unc_vars_factor.insert(vc);
      }
    }
    else if (!v.isVar() || (!var.isNull() && var != v))
    {
      Trace("nl-ext-cms-debug")
          << "...invalid due to factor " << v << std::endl;
      // cannot solve multivariate
      if (is_valid)
      {
        is_valid = false;
        // if b is non-zero, then var is also an unconstrained variable
        if (b != d_zero)
        {
          unc_vars.insert(var);
          unc_vars_factor.insert(var);
        }
      }
      // if v is unconstrained, we may turn this equality into a substitution
      unc_vars.insert(v);
      unc_vars_factor.insert(v);
    }
    else
    {
      // set the variable to solve for
      b = coeff;
      var = v;
    }
  }
  if (!is_valid)
  {
    // see if we can solve for a variable?
    for (const Node& uv : unc_vars)
    {
      Trace("nl-ext-cm-debug") << "check subs var : " << uv << std::endl;
      // cannot already have a bound
      if (uv.isVar() && !hasAssignment(uv))
      {
        Node slv;
        Node veqc;
        if (ArithMSum::isolate(uv, msum, veqc, slv, EQUAL) != 0)
        {
          Assert(!slv.isNull());
          // must rewrite here to be in substituted form
          slv = rewrite(slv);
          // Currently do not support substitution-with-coefficients.
          // We also ensure types are correct here, which avoids substituting
          // a term of non-integer type for a variable of integer type.
          if (veqc.isNull() && !expr::hasSubterm(slv, uv)
              && slv.getType() == uv.getType())
          {
            Trace("nl-ext-cm")
                << "check-model-subs : " << uv << " -> " << slv << std::endl;
            bool ret = addSubstitution(uv, slv);
            if (ret)
            {
              Trace("nl-ext-cms") << "...success, model substitution " << uv
                                  << " -> " << slv << std::endl;
              d_check_model_solved[eq] = uv;
            }
            return ret;
          }
        }
      }
    }
    // see if we can assign a variable to a constant
    for (const Node& uvf : unc_vars_factor)
    {
      Trace("nl-ext-cm-debug") << "check set var : " << uvf << std::endl;
      // cannot already have a bound
      if (uvf.isVar() && !hasAssignment(uvf))
      {
        Node uvfv = computeConcreteModelValue(uvf);
        // fail if model value is non-constant
        if (!uvfv.isConst())
        {
          return false;
        }
        if (TraceIsOn("nl-ext-cm"))
        {
          Trace("nl-ext-cm") << "check-model-bound : exact : " << uvf << " = ";
          printRationalApprox("nl-ext-cm", uvfv);
          Trace("nl-ext-cm") << std::endl;
        }
        bool ret = addSubstitution(uvf, uvfv);
        // recurse
        return ret ? solveEqualitySimple(eq, d, lemmas) : false;
      }
    }
    Trace("nl-ext-cms") << "...fail due to constrained invalid terms."
                        << std::endl;
    return false;
  }
  else if (var.isNull() || var.getType().isInteger())
  {
    // cannot solve quadratic equations for integer variables
    Trace("nl-ext-cms") << "...fail due to variable to solve for." << std::endl;
    return false;
  }

  // we are linear, it is simple
  if (b == d_zero)
  {
    Trace("nl-ext-cms") << "...fail due to zero a/b." << std::endl;
    Assert(false);
    return false;
  }
  Node val = nm->mkConstReal(-c.getConst<Rational>() / b.getConst<Rational>());
  if (TraceIsOn("nl-ext-cm"))
  {
    Trace("nl-ext-cm") << "check-model-bound : exact : " << var << " = ";
    printRationalApprox("nl-ext-cm", val);
    Trace("nl-ext-cm") << std::endl;
  }
  bool ret = addSubstitution(var, val);
  if (ret)
  {
    Trace("nl-ext-cms") << "...success, solved linear." << std::endl;
    d_check_model_solved[eq] = var;
  }
  return ret;
}

bool NlModel::simpleCheckModelLit(Node lit)
{
  Trace("nl-ext-cms") << "*** Simple check-model lit for " << lit << "..."
                      << std::endl;
  if (lit.isConst())
  {
    Trace("nl-ext-cms") << "  return constant." << std::endl;
    return lit.getConst<bool>();
  }
  NodeManager* nm = NodeManager::currentNM();
  bool pol = lit.getKind() != kind::NOT;
  Node atom = lit.getKind() == kind::NOT ? lit[0] : lit;

  if (atom.getKind() == EQUAL)
  {
    // x = a is ( x >= a ^ x <= a )
    for (unsigned i = 0; i < 2; i++)
    {
      Node lit2 = nm->mkNode(GEQ, atom[i], atom[1 - i]);
      if (!pol)
      {
        lit2 = lit2.negate();
      }
      lit2 = rewrite(lit2);
      bool success = simpleCheckModelLit(lit2);
      if (success != pol)
      {
        // false != true -> one conjunct of equality is false, we fail
        // true != false -> one disjunct of disequality is true, we succeed
        return success;
      }
    }
    // both checks passed and polarity is true, or both checks failed and
    // polarity is false
    return pol;
  }
  else if (atom.getKind() != GEQ)
  {
    Trace("nl-ext-cms") << "  failed due to unknown literal." << std::endl;
    return false;
  }
  // get the monomial sum
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(atom, msum))
  {
    Trace("nl-ext-cms") << "  failed due to get msum." << std::endl;
    return false;
  }
  // simple interval analysis
  if (simpleCheckModelMsum(msum, pol))
  {
    return true;
  }
  // can also try reasoning about univariate quadratic equations
  Trace("nl-ext-cms-debug")
      << "* Try univariate quadratic analysis..." << std::endl;
  std::vector<Node> vs_invalid;
  std::unordered_set<Node> vs;
  std::map<Node, Node> v_a;
  std::map<Node, Node> v_b;
  // get coefficients...
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    if (!v.isNull())
    {
      if (v.isVar())
      {
        v_b[v] = m.second.isNull() ? d_one : m.second;
        vs.insert(v);
      }
      else if (v.getKind() == NONLINEAR_MULT && v.getNumChildren() == 2
               && v[0] == v[1] && v[0].isVar())
      {
        v_a[v[0]] = m.second.isNull() ? d_one : m.second;
        vs.insert(v[0]);
      }
      else
      {
        vs_invalid.push_back(v);
      }
    }
  }
  // solve the valid variables...
  Node invalid_vsum = vs_invalid.empty() ? d_zero
                                         : (vs_invalid.size() == 1
                                                ? vs_invalid[0]
                                                : nm->mkNode(ADD, vs_invalid));
  // substitution to try
  ArithSubs qsub;
  for (const Node& v : vs)
  {
    // is it a valid variable?
    std::map<Node, std::pair<Node, Node>>::iterator bit =
        d_check_model_bounds.find(v);
    if (!expr::hasSubterm(invalid_vsum, v) && bit != d_check_model_bounds.end())
    {
      std::map<Node, Node>::iterator it = v_a.find(v);
      if (it != v_a.end())
      {
        Node a = it->second;
        Assert(a.isConst());
        int asgn = a.getConst<Rational>().sgn();
        Assert(asgn != 0);
        Node t = nm->mkNode(MULT, a, v, v);
        Node b = d_zero;
        it = v_b.find(v);
        if (it != v_b.end())
        {
          b = it->second;
          t = nm->mkNode(ADD, t, nm->mkNode(MULT, b, v));
        }
        t = rewrite(t);
        Trace("nl-ext-cms-debug") << "Trying to find min/max for quadratic "
                                  << t << "..." << std::endl;
        Trace("nl-ext-cms-debug") << "    a = " << a << std::endl;
        Trace("nl-ext-cms-debug") << "    b = " << b << std::endl;
        // find maximal/minimal value on the interval
        Node apex = nm->mkNode(
            DIVISION, nm->mkNode(NEG, b), nm->mkNode(MULT, d_two, a));
        apex = rewrite(apex);
        Assert(apex.isConst());
        // for lower, upper, whether we are greater than the apex
        bool cmp[2];
        Node boundn[2];
        for (unsigned r = 0; r < 2; r++)
        {
          boundn[r] = r == 0 ? bit->second.first : bit->second.second;
          Node cmpn = nm->mkNode(GT, boundn[r], apex);
          cmpn = rewrite(cmpn);
          Assert(cmpn.isConst());
          cmp[r] = cmpn.getConst<bool>();
        }
        Trace("nl-ext-cms-debug") << "  apex " << apex << std::endl;
        Trace("nl-ext-cms-debug")
            << "  lower " << boundn[0] << ", cmp: " << cmp[0] << std::endl;
        Trace("nl-ext-cms-debug")
            << "  upper " << boundn[1] << ", cmp: " << cmp[1] << std::endl;
        Assert(boundn[0].getConst<Rational>()
               <= boundn[1].getConst<Rational>());
        Node s;
        qsub.addArith(v, Node());
        if (cmp[0] != cmp[1])
        {
          Assert(!cmp[0] && cmp[1]);
          // does the sign match the bound?
          if ((asgn == 1) == pol)
          {
            // the apex is the max/min value
            s = apex;
            Trace("nl-ext-cms-debug") << "  ...set to apex." << std::endl;
          }
          else
          {
            // it is one of the endpoints, plug in and compare
            Node tcmpn[2];
            for (unsigned r = 0; r < 2; r++)
            {
              qsub.d_subs.back() = boundn[r];
              Node ts = qsub.applyArith(t);
              tcmpn[r] = rewrite(ts);
            }
            Node tcmp = nm->mkNode(LT, tcmpn[0], tcmpn[1]);
            Trace("nl-ext-cms-debug")
                << "  ...both sides of apex, compare " << tcmp << std::endl;
            tcmp = rewrite(tcmp);
            Assert(tcmp.isConst());
            unsigned bindex_use = (tcmp.getConst<bool>() == pol) ? 1 : 0;
            Trace("nl-ext-cms-debug")
                << "  ...set to " << (bindex_use == 1 ? "upper" : "lower")
                << std::endl;
            s = boundn[bindex_use];
          }
        }
        else
        {
          // both to one side of the apex
          // we figure out which bound to use (lower or upper) based on
          // three factors:
          // (1) whether a's sign is positive,
          // (2) whether we are greater than the apex of the parabola,
          // (3) the polarity of the constraint, i.e. >= or <=.
          // there are 8 cases of these factors, which we test here.
          unsigned bindex_use = (((asgn == 1) == cmp[0]) == pol) ? 0 : 1;
          Trace("nl-ext-cms-debug")
              << "  ...set to " << (bindex_use == 1 ? "upper" : "lower")
              << std::endl;
          s = boundn[bindex_use];
        }
        Assert(!s.isNull());
        qsub.d_subs.back() = s;
        Trace("nl-ext-cms") << "* set bound based on quadratic : " << v
                            << " -> " << s << std::endl;
      }
    }
  }
  if (!qsub.empty())
  {
    Node slit = qsub.applyArith(lit);
    slit = rewrite(slit);
    return simpleCheckModelLit(slit);
  }
  return false;
}

bool NlModel::simpleCheckModelMsum(const std::map<Node, Node>& msum, bool pol)
{
  Trace("nl-ext-cms-debug") << "* Try simple interval analysis..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // map from transcendental functions to whether they were set to lower
  // bound
  bool simpleSuccess = true;
  std::map<Node, bool> set_bound;
  std::vector<Node> sum_bound;
  for (const std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    if (v.isNull())
    {
      sum_bound.push_back(m.second.isNull() ? d_one : m.second);
    }
    else
    {
      Trace("nl-ext-cms-debug") << "- monomial : " << v << std::endl;
      // --- whether we should set a lower bound for this monomial
      bool set_lower =
          (m.second.isNull() || m.second.getConst<Rational>().sgn() == 1)
          == pol;
      Trace("nl-ext-cms-debug")
          << "set bound to " << (set_lower ? "lower" : "upper") << std::endl;

      // --- Collect variables and factors in v
      std::vector<Node> vars;
      std::vector<unsigned> factors;
      if (v.getKind() == NONLINEAR_MULT)
      {
        unsigned last_start = 0;
        for (unsigned i = 0, nchildren = v.getNumChildren(); i < nchildren; i++)
        {
          // are we at the end?
          if (i + 1 == nchildren || v[i + 1] != v[i])
          {
            unsigned vfact = 1 + (i - last_start);
            last_start = (i + 1);
            vars.push_back(v[i]);
            factors.push_back(vfact);
          }
        }
      }
      else
      {
        vars.push_back(v);
        factors.push_back(1);
      }

      // --- Get the lower and upper bounds and sign information.
      // Whether we have an (odd) number of negative factors in vars, apart
      // from the variable at choose_index.
      bool has_neg_factor = false;
      int choose_index = -1;
      std::vector<Node> ls;
      std::vector<Node> us;
      // the relevant sign information for variables with odd exponents:
      //   1: both signs of the interval of this variable are positive,
      //  -1: both signs of the interval of this variable are negative.
      std::vector<int> signs;
      Trace("nl-ext-cms-debug") << "get sign information..." << std::endl;
      for (unsigned i = 0, size = vars.size(); i < size; i++)
      {
        Node vc = vars[i];
        unsigned vcfact = factors[i];
        if (TraceIsOn("nl-ext-cms-debug"))
        {
          Trace("nl-ext-cms-debug") << "-- " << vc;
          if (vcfact > 1)
          {
            Trace("nl-ext-cms-debug") << "^" << vcfact;
          }
          Trace("nl-ext-cms-debug") << " ";
        }
        std::map<Node, std::pair<Node, Node>>::iterator bit =
            d_check_model_bounds.find(vc);
        // if there is a model bound for this term
        if (bit != d_check_model_bounds.end())
        {
          Node l = bit->second.first;
          Node u = bit->second.second;
          ls.push_back(l);
          us.push_back(u);
          int vsign = 0;
          if (vcfact % 2 == 1)
          {
            vsign = 1;
            int lsgn = l.getConst<Rational>().sgn();
            int usgn = u.getConst<Rational>().sgn();
            Trace("nl-ext-cms-debug")
                << "bound_sign(" << lsgn << "," << usgn << ") ";
            if (lsgn == -1)
            {
              if (usgn < 1)
              {
                // must have a negative factor
                has_neg_factor = !has_neg_factor;
                vsign = -1;
              }
              else if (choose_index == -1)
              {
                // set the choose index to this
                choose_index = i;
                vsign = 0;
              }
              else
              {
                // ambiguous, can't determine the bound
                Trace("nl-ext-cms")
                    << "  failed due to ambiguious monomial." << std::endl;
                return false;
              }
            }
          }
          Trace("nl-ext-cms-debug") << " -> " << vsign << std::endl;
          signs.push_back(vsign);
        }
        else
        {
          Trace("nl-ext-cms-debug") << std::endl;
          Trace("nl-ext-cms")
              << "  failed due to unknown bound for " << vc << std::endl;
          // should either assign a model bound or eliminate the variable
          // via substitution
          Assert(false) << "A variable " << vc
                        << " is missing a bound/value in the model";
          return false;
        }
      }
      // whether we will try to minimize/maximize (-1/1) the absolute value
      int setAbs = (set_lower == has_neg_factor) ? 1 : -1;
      Trace("nl-ext-cms-debug")
          << "set absolute value to " << (setAbs == 1 ? "maximal" : "minimal")
          << std::endl;

      std::vector<Node> vbs;
      Trace("nl-ext-cms-debug") << "set bounds..." << std::endl;
      for (unsigned i = 0, size = vars.size(); i < size; i++)
      {
        Node vc = vars[i];
        unsigned vcfact = factors[i];
        Node l = ls[i];
        Node u = us[i];
        bool vc_set_lower;
        int vcsign = signs[i];
        Trace("nl-ext-cms-debug")
            << "Bounds for " << vc << " : " << l << ", " << u
            << ", sign : " << vcsign << ", factor : " << vcfact << std::endl;
        if (l == u)
        {
          // by convention, always say it is lower if they are the same
          vc_set_lower = true;
          Trace("nl-ext-cms-debug")
              << "..." << vc << " equal bound, set to lower" << std::endl;
        }
        else
        {
          if (vcfact % 2 == 0)
          {
            // minimize or maximize its absolute value
            Rational la = l.getConst<Rational>().abs();
            Rational ua = u.getConst<Rational>().abs();
            if (la == ua)
            {
              // by convention, always say it is lower if abs are the same
              vc_set_lower = true;
              Trace("nl-ext-cms-debug")
                  << "..." << vc << " equal abs, set to lower" << std::endl;
            }
            else
            {
              vc_set_lower = (la > ua) == (setAbs == 1);
            }
          }
          else if (signs[i] == 0)
          {
            // we choose this index to match the overall set_lower
            vc_set_lower = set_lower;
          }
          else
          {
            vc_set_lower = (signs[i] != setAbs);
          }
          Trace("nl-ext-cms-debug")
              << "..." << vc << " set to " << (vc_set_lower ? "lower" : "upper")
              << std::endl;
        }
        // check whether this is a conflicting bound
        std::map<Node, bool>::iterator itsb = set_bound.find(vc);
        if (itsb == set_bound.end())
        {
          set_bound[vc] = vc_set_lower;
        }
        else if (itsb->second != vc_set_lower)
        {
          Trace("nl-ext-cms")
              << "  failed due to conflicting bound for " << vc << std::endl;
          return false;
        }
        // must over/under approximate based on vc_set_lower, computed above
        Node vb = vc_set_lower ? l : u;
        for (unsigned i2 = 0; i2 < vcfact; i2++)
        {
          vbs.push_back(vb);
        }
      }
      if (!simpleSuccess)
      {
        break;
      }
      Node vbound = vbs.size() == 1 ? vbs[0] : nm->mkNode(MULT, vbs);
      sum_bound.push_back(ArithMSum::mkCoeffTerm(m.second, vbound));
    }
  }
  // if the exact bound was computed via simple analysis above
  // make the bound
  Node bound;
  if (sum_bound.size() > 1)
  {
    bound = nm->mkNode(kind::ADD, sum_bound);
  }
  else if (sum_bound.size() == 1)
  {
    bound = sum_bound[0];
  }
  else
  {
    bound = d_zero;
  }
  // make the comparison
  Node comp = nm->mkNode(kind::GEQ, bound, d_zero);
  if (!pol)
  {
    comp = comp.negate();
  }
  Trace("nl-ext-cms") << "  comparison is : " << comp << std::endl;
  comp = rewrite(comp);
  Assert(comp.isConst());
  Trace("nl-ext-cms") << "  returned : " << comp << std::endl;
  return comp == d_true;
}

void NlModel::printModelValue(const char* c, Node n, unsigned prec) const
{
  if (TraceIsOn(c))
  {
    Trace(c) << "  " << n << " -> ";
    const Node& aval = d_abstractModelCache.at(n);
    if (aval.isConst())
    {
      printRationalApprox(c, aval, prec);
    }
    else
    {
      Trace(c) << "?";
    }
    Trace(c) << " [actual: ";
    const Node& cval = d_concreteModelCache.at(n);
    if (cval.isConst())
    {
      printRationalApprox(c, cval, prec);
    }
    else
    {
      Trace(c) << "?";
    }
    Trace(c) << " ]" << std::endl;
  }
}

void NlModel::getModelValueRepair(std::map<Node, Node>& arithModel)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-model") << "NlModel::getModelValueRepair:" << std::endl;
  // If we extended the model with entries x -> 0 for unconstrained values,
  // we first update the map to the extended one.
  if (d_arithVal.size() > arithModel.size())
  {
    arithModel = d_arithVal;
  }
  // Record the approximations we used. This code calls the
  // recordApproximation method of the model, which overrides the model
  // values for variables that we solved for, using techniques specific to
  // this class.
  for (const std::pair<const Node, std::pair<Node, Node>>& cb :
       d_check_model_bounds)
  {
    Node l = cb.second.first;
    Node u = cb.second.second;
    Node v = cb.first;
    if (l != u)
    {
      Trace("nl-model") << v << " is in interval " << l << "..." << u
                        << std::endl;
    }
    else
    {
      // overwrite, ensure the type is correct
      Assert(l.isConst());
      Node ll = nm->mkConstRealOrInt(v.getType(), l.getConst<Rational>());
      arithModel[v] = ll;
      Trace("nl-model") << v << " exact approximation is " << ll << std::endl;
    }
  }
  // Also record the exact values we used. An exact value can be seen as a
  // special kind approximation of the form (witness x. x = exact_value).
  // Notice that the above term gets rewritten such that the choice function
  // is eliminated.
  for (size_t i = 0; i < d_substitutions.size(); ++i)
  {
    // overwrite, ensure the type is correct
    Node v = d_substitutions.d_vars[i];
    Node s = d_substitutions.d_subs[i];
    Node ss = s;
    // If its a rational constant, ensure it has the proper type now. It
    // also may be a RAN, in which case v should be a real.
    if (s.isConst())
    {
      ss = nm->mkConstRealOrInt(v.getType(), s.getConst<Rational>());
    }
    arithModel[v] = ss;
    Trace("nl-model") << v << " solved is " << ss << std::endl;
  }

  // multiplication terms should not be given values; their values are
  // implied by the monomials that they consist of
  std::vector<Node> amErase;
  for (const std::pair<const Node, Node>& am : arithModel)
  {
    if (am.first.getKind() == NONLINEAR_MULT)
    {
      amErase.push_back(am.first);
    }
  }
  for (const Node& ae : amErase)
  {
    arithModel.erase(ae);
  }
}

Node NlModel::getValueInternal(TNode n)
{
  if (n.isConst())
  {
    return n;
  }
  if (auto it = d_arithVal.find(n); it != d_arithVal.end())
  {
    AlwaysAssert(it->second.isConst());
    return it->second;
  }
  // It is unconstrained in the model, return 0. We additionally add it
  // to mapping from the linear solver. This ensures that if the nonlinear
  // solver assumes that n = 0, then this assumption is recorded in the overall
  // model.
  Node zero = mkZero(n.getType());
  d_arithVal[n] = zero;
  return zero;
}

bool NlModel::hasAssignment(Node v) const
{
  if (d_check_model_bounds.find(v) != d_check_model_bounds.end())
  {
    return true;
  }
  return (d_substitutions.contains(v));
}

bool NlModel::hasLinearModelValue(TNode v, Node& val) const
{
  auto it = d_arithVal.find(v);
  if (it != d_arithVal.end())
  {
    val = it->second;
    return true;
  }
  return false;
}

Node NlModel::getSubstitutedForm(TNode s) const
{
  if (d_substitutions.empty())
  {
    // no substitutions, just return s
    return s;
  }
  return rewrite(d_substitutions.applyArith(s));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
