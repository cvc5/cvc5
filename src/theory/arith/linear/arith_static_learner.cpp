/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic static learner
 */

#include "theory/arith/linear/arith_static_learner.h"

#include <vector>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/arith/arith_proof_utilities.h"
#include "theory/arith/arith_utilities.h"
#include "util/statistics_registry.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

ArithStaticLearner::ArithStaticLearner(Env& env)
    : EnvObj(env),
      d_minMap(userContext()),
      d_maxMap(userContext()),
      d_statistics(statisticsRegistry())
{
}

ArithStaticLearner::~ArithStaticLearner(){
}

ArithStaticLearner::Statistics::Statistics(StatisticsRegistry& sr)
    : d_iteMinMaxApplications(
        sr.registerInt("theory::arith::iteMinMaxApplications")),
      d_iteConstantApplications(
          sr.registerInt("theory::arith::iteConstantApplications"))
{
}

void ArithStaticLearner::staticLearning(TNode n,
                                        std::vector<TrustNode>& learned)
{
  vector<TNode> workList;
  workList.push_back(n);
  TNodeSet processed;

  //Contains an underapproximation of nodes that must hold.
  TNodeSet defTrue;

  defTrue.insert(n);

  while(!workList.empty()) {
    n = workList.back();

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }
    if (n.getKind() == Kind::AND && defTrue.find(n) != defTrue.end())
    {
      for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
        defTrue.insert(*i);
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    process(n,learned, defTrue);

  }
}

void ArithStaticLearner::process(TNode n,
                                 std::vector<TrustNode>& learned,
                                 const TNodeSet& defTrue)
{
  Trace("arith::static") << "===================== looking at " << n << endl;

  switch(n.getKind()){
    case Kind::ITE:
      if (expr::hasBoundVar(n))
      {
        // Unsafe with non-ground ITEs; do nothing
        Trace("arith::static")
            << "(potentially) non-ground ITE, ignoring..." << endl;
        break;
      }

      if (n[0].getKind() != Kind::EQUAL && isRelationOperator(n[0].getKind()))
      {
        iteMinMax(n, learned);
      }

      if ((d_minMap.find(n[1]) != d_minMap.end()
           && d_minMap.find(n[2]) != d_minMap.end())
          || (d_maxMap.find(n[1]) != d_maxMap.end()
              && d_maxMap.find(n[2]) != d_maxMap.end()))
      {
        iteConstant(n, learned);
      }
      break;

    case Kind::CONST_RATIONAL:
    case Kind::CONST_INTEGER:
      // Mark constants as minmax
      d_minMap.insert(n, n.getConst<Rational>());
      d_maxMap.insert(n, n.getConst<Rational>());
      break;
    default:  // Do nothing
      break;
  }
}

void ArithStaticLearner::iteMinMax(TNode n, std::vector<TrustNode>& learned)
{
  Assert(n.getKind() == Kind::ITE);
  Assert(n[0].getKind() != Kind::EQUAL);
  Assert(isRelationOperator(n[0].getKind()));

  NodeManager* nm = n.getNodeManager();

  TNode c = n[0];
  Kind k = oldSimplifiedKind(c);
  TNode t = n[1];
  TNode e = n[2];
  TNode cleft = (c.getKind() == Kind::NOT) ? c[0][0] : c[0];
  TNode cright = (c.getKind() == Kind::NOT) ? c[0][1] : c[1];

  if((t == cright) && (e == cleft)){
    TNode tmp = t;
    t = e;
    e = tmp;
    k = reverseRelationKind(k);
  }
  //(ite (< x y) x y)
  //(ite (x < y) x y)
  //(ite (x - y < 0) x y)
  // ----------------
  // (ite (x - y < -c) )

  if(t == cleft && e == cright){
    // t == cleft && e == cright
    Assert(t == cleft);
    Assert(e == cright);
    switch(k){
      case Kind::LT:  // (ite (< x y) x y)
      case Kind::LEQ:
      {  // (ite (<= x y) x y)
        Node nLeqX = NodeBuilder(nm, Kind::LEQ) << n << t;
        Node nLeqY = NodeBuilder(nm, Kind::LEQ) << n << e;
        Trace("arith::static")
            << n << " is a min =>" << nLeqX << " " << nLeqY << endl;
        addLearnedLemma(nLeqX, learned);
        addLearnedLemma(nLeqY, learned);
        ++(d_statistics.d_iteMinMaxApplications);
        break;
      }
      case Kind::GT:  // (ite (> x y) x y)
      case Kind::GEQ:
      {  // (ite (>= x y) x y)
        Node nGeqX = NodeBuilder(nm, Kind::GEQ) << n << t;
        Node nGeqY = NodeBuilder(nm, Kind::GEQ) << n << e;
        Trace("arith::static")
            << n << " is a max =>" << nGeqX << " " << nGeqY << endl;
        addLearnedLemma(nGeqX, learned);
        addLearnedLemma(nGeqY, learned);
        ++(d_statistics.d_iteMinMaxApplications);
        break;
      }
    default: Unreachable();
    }
  }
}

void ArithStaticLearner::iteConstant(TNode n, std::vector<TrustNode>& learned)
{
  Assert(n.getKind() == Kind::ITE);

  Trace("arith::static") << "iteConstant(" << n << ")" << endl;

  if (d_minMap.find(n[1]) != d_minMap.end() && d_minMap.find(n[2]) != d_minMap.end()) {
    const DeltaRational& first = d_minMap[n[1]];
    const DeltaRational& second = d_minMap[n[2]];
    DeltaRational min = std::min(first, second);
    CDNodeToMinMaxMap::const_iterator minFind = d_minMap.find(n);
    if (minFind == d_minMap.end() || (*minFind).second < min) {
      d_minMap.insert(n, min);
      NodeManager* nm = NodeManager::currentNM();
      Node nGeqMin = nm->mkNode(
          min.getInfinitesimalPart() == 0 ? Kind::GEQ : Kind::GT,
          n,
          nm->mkConstRealOrInt(n.getType(), min.getNoninfinitesimalPart()));
      // To ensure that proofs and unsat cores can be used with this class,
      // we require the assertions added by this class are valid. Thus, if
      // c > 5 is a top-level assertion, instead of adding:
      //   (ite A c 4) >= 4
      // noting that c is entailed greater than 4, we add the valid fact:
      //   (c > 5) => (ite A c 4) >= 4
      // The latter is slightly less efficient since it requires e.g.
      // resolving the disjunction with c > 5, but is preferred to make this
      // compatible with proofs and unsat cores.
      std::vector<Node> conj;
      if (!n[1].isConst())
      {
        conj.push_back(
            nm->mkNode(first.getInfinitesimalPart() == 0 ? Kind::GEQ : Kind::GT,
                       n[1],
                       nm->mkConstRealOrInt(n.getType(),
                                            first.getNoninfinitesimalPart())));
      }
      if (!n[2].isConst())
      {
        conj.push_back(nm->mkNode(
            second.getInfinitesimalPart() == 0 ? Kind::GEQ : Kind::GT,
            n[2],
            nm->mkConstRealOrInt(n.getType(),
                                 second.getNoninfinitesimalPart())));
      }
      nGeqMin = conj.empty()
                    ? nGeqMin
                    : nm->mkNode(Kind::IMPLIES, nm->mkAnd(conj), nGeqMin);
      addLearnedLemma(nGeqMin, learned);
      Trace("arith::static") << n << " iteConstant"  << nGeqMin << endl;
      ++(d_statistics.d_iteConstantApplications);
    }
  }

  if (d_maxMap.find(n[1]) != d_maxMap.end() && d_maxMap.find(n[2]) != d_maxMap.end()) {
    const DeltaRational& first = d_maxMap[n[1]];
    const DeltaRational& second = d_maxMap[n[2]];
    DeltaRational max = std::max(first, second);
    CDNodeToMinMaxMap::const_iterator maxFind = d_maxMap.find(n);
    if (maxFind == d_maxMap.end() || (*maxFind).second > max) {
      d_maxMap.insert(n, max);
      NodeManager* nm = NodeManager::currentNM();
      Node nLeqMax = nm->mkNode(
          max.getInfinitesimalPart() == 0 ? Kind::LEQ : Kind::LT,
          n,
          nm->mkConstRealOrInt(n.getType(), max.getNoninfinitesimalPart()));
      // Similar to above, we ensure the assertion we are adding is valid for
      // the purposes of proofs and unsat cores.
      std::vector<Node> conj;
      if (!n[1].isConst())
      {
        conj.push_back(
            nm->mkNode(first.getInfinitesimalPart() == 0 ? Kind::LEQ : Kind::LT,
                       n[1],
                       nm->mkConstRealOrInt(n.getType(),
                                            first.getNoninfinitesimalPart())));
      }
      if (!n[2].isConst())
      {
        conj.push_back(nm->mkNode(
            second.getInfinitesimalPart() == 0 ? Kind::LEQ : Kind::LT,
            n[2],
            nm->mkConstRealOrInt(n.getType(),
                                 second.getNoninfinitesimalPart())));
      }
      nLeqMax = conj.empty()
                    ? nLeqMax
                    : nm->mkNode(Kind::IMPLIES, nm->mkAnd(conj), nLeqMax);
      addLearnedLemma(nLeqMax, learned);
      Trace("arith::static") << n << " iteConstant"  << nLeqMax << endl;
      ++(d_statistics.d_iteConstantApplications);
    }
  }
}

std::set<Node> listToSet(TNode l){
  std::set<Node> ret;
  while (l.getKind() == Kind::OR)
  {
    Assert(l.getNumChildren() == 2);
    ret.insert(l[0]);
    l = l[1];
  }
  return ret;
}

void ArithStaticLearner::addBound(TNode n) {

  CDNodeToMinMaxMap::const_iterator minFind = d_minMap.find(n[0]);
  CDNodeToMinMaxMap::const_iterator maxFind = d_maxMap.find(n[0]);

  Rational constant = n[1].getConst<Rational>();
  DeltaRational bound = constant;

  switch(Kind k = n.getKind()) {
    case Kind::LT: bound = DeltaRational(constant, -1); CVC5_FALLTHROUGH;
    case Kind::LEQ:
      if (maxFind == d_maxMap.end() || (*maxFind).second > bound)
      {
        d_maxMap.insert(n[0], bound);
        Trace("arith::static") << "adding bound " << n << endl;
      }
      break;
    case Kind::GT: bound = DeltaRational(constant, 1); CVC5_FALLTHROUGH;
    case Kind::GEQ:
      if (minFind == d_minMap.end() || (*minFind).second < bound)
      {
        d_minMap.insert(n[0], bound);
        Trace("arith::static") << "adding bound " << n << endl;
      }
      break;
    default: Unhandled() << k; break;
  }
}

void ArithStaticLearner::addLearnedLemma(TNode n,
                                         std::vector<TrustNode>& learned)
{
  TrustNode trn = TrustNode::mkTrustLemma(n, this);
  learned.emplace_back(trn);
}

std::shared_ptr<ProofNode> ArithStaticLearner::getProofFor(Node fact)
{
  Trace("arith-static-pf") << "Prove: " << fact << std::endl;
  std::vector<Node> antec;
  Node conc = fact;
  // maps arithmetic variables to their constraints in the antecedant
  std::map<Node, Node> amap;
  if (fact.getKind() == Kind::IMPLIES)
  {
    if (fact[0].getKind() == Kind::AND)
    {
      antec.insert(antec.end(), fact[0].begin(), fact[0].end());
    }
    else
    {
      antec.push_back(fact[0]);
    }
    conc = fact[1];
    for (const Node& a : antec)
    {
      Assert(a.getNumChildren() == 2 && a[1].isConst());
      amap[a[0]] = a;
    }
  }
  Kind ck = conc.getKind();
  Assert(conc.getNumChildren() == 2 && conc[0].getKind() == Kind::ITE);
  NodeManager* nm = nodeManager();
  CDProof cdp(d_env);
  Node cond = conc[0][0];
  Node truen = nm->mkConst(true);
  // if we are (<rel1> (ite (<rel2> s t) t s) r) where r is s|t.
  if (cond.getNumChildren() == 2 && cond[0] == conc[0][2]
      && cond[1] == conc[0][1]
      && (conc[1] == conc[0][1] || conc[1] == conc[0][2]))
  {
    Trace("arith-static-pf") << "(Flipped) min/max term..." << std::endl;
    // flip relation, likely a min/max term.
    // the transformation below turns e.g.
    // (>= (ite (< s t) t s) t) into (>= (ite (>= s t) s t) t)
    Kind crk = negateKind(cond.getKind());
    Node iteFlip = nm->mkNode(
        Kind::ITE, nm->mkNode(crk, cond[0], cond[1]), conc[0][2], conc[0][1]);
    Node iteFlipN =
        nm->mkNode(Kind::ITE, cond.negate(), conc[0][2], conc[0][1]);
    Node eq1 = conc[0].eqNode(iteFlipN);
    // shown by RARE rule ite-not-cond
    cdp.addTrustedStep(eq1, TrustId::ARITH_STATIC_LEARN, {}, {});
    Trace("arith-static-pf") << "- subgoal " << eq1 << std::endl;
    Node eq2 = iteFlipN.eqNode(iteFlip);
    if (rewrite(eq2) == truen)
    {
      // shown by rewriting
      cdp.addStep(eq2, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq2});
      Node eqt = conc[0].eqNode(iteFlip);
      // ------------------------------------ ite-not-cond, MACRO_SR_PRED_INTRO
      // (ite (< s t) t s) = (ite (not (< s t)) s t) = (ite (>= s t) s t)
      // ---------------------------------------------------------------- TRANS
      // (ite (< s t) t s) = (ite (>= s t) s t)
      cdp.addStep(eqt, ProofRule::TRANS, {eq1, eq2}, {});
      Node eqrefl = conc[1].eqNode(conc[1]);
      cdp.addStep(eqrefl, ProofRule::REFL, {}, {conc[1]});
      std::vector<Node> congPremises;
      congPremises.push_back(eqt);
      congPremises.push_back(eqrefl);
      Node npred = nm->mkNode(conc.getKind(), iteFlip, conc[1]);
      std::vector<Node> cargs;
      ProofRule cr = expr::getCongRule(conc, cargs);
      Node equiv = conc.eqNode(npred);
      // ------------------------------------- from above  ------ REFL
      // (ite (< s t) t s) = (ite (>= s t) s t)             t = t
      // -------------------------------------------------------- CONG
      // (>= (ite (< s t) t s) t) = (>= (ite (>= s t) s t) t)
      cdp.addStep(equiv, cr, congPremises, cargs);
      Node equivs = npred.eqNode(conc);
      cdp.addStep(equivs, ProofRule::SYMM, {equiv}, {});
      // npred can be shown by a RARE rule arith-{min,max}-*
      cdp.addTrustedStep(npred, TrustId::ARITH_STATIC_LEARN, {}, {});
      //                          -------------------------- from above
      //                          (>= (ite (< s t) t s) t) = (>= I t)
      // ------ arith-{min,max}-* ----------------------------------- SYMM
      // (>= I t)                 (>= I t) = (>= (ite (< s t) t s) t)
      // ---------------------------------------------------- EQ_RESOLVE
      // (>= (ite (< s t) t s) t)
      // where I is (ite (>= s t) s t).
      Trace("arith-static-pf") << "- subgoal " << npred << std::endl;
      cdp.addStep(conc, ProofRule::EQ_RESOLVE, {npred, equivs}, {});
    }
    else
    {
      // this should always hold unless the rewriter for ITE changes
      Assert(false) << "...failed rewrite " << eq2 << std::endl;
      cdp.addTrustedStep(fact, TrustId::ARITH_STATIC_LEARN, {}, {});
      return cdp.getProofFor(fact);
    }
  }
  else if (cond.getNumChildren() == 2 && cond[0] == conc[0][1]
           && cond[1] == conc[0][2]
           && (conc[1] == conc[0][1] || conc[1] == conc[0][2]))
  {
    // if we are (<rel1> (ite (<rel2> s t) s t) r) where r is s|t.
    Trace("arith-static-pf") << "Min/max term..." << std::endl;
    // conc can be shown by a RARE rule arith-{min,max}-*
    cdp.addTrustedStep(conc, TrustId::ARITH_STATIC_LEARN, {}, {});
  }
  else
  {
    // otherwise we are (=> (and R1? R2?) (<rel> (ite C s t) c)) where either
    // - R1 is not provided and s is a value such that (<rel> s c) is true
    // - R1 is provided and implies (<rel> s c).
    // Similarly for t and R2.
    std::vector<Node> branches;
    std::vector<Node> congPremises;
    Node ceq = cond.eqNode(cond);
    congPremises.push_back(ceq);
    cdp.addStep(ceq, ProofRule::REFL, {}, {cond});
    std::map<Node, Node>::iterator ita;
    // prove the branches
    for (size_t i = 1; i <= 2; i++)
    {
      Node b = nm->mkNode(ck, conc[0][i], conc[1]);
      branches.push_back(b);
      Node beval = evaluate(b, {}, {}, false);
      Node eq = b.eqNode(truen);
      congPremises.push_back(eq);
      if (beval == truen)
      {
        cdp.addStep(eq, ProofRule::EVALUATE, {}, {b});
      }
      else
      {
        ita = amap.find(conc[0][i]);
        if (ita != amap.end())
        {
          // after lifting, the branch may be an antecedant
          if (ita->second == b)
          {
            cdp.addStep(eq, ProofRule::TRUE_INTRO, {ita->second}, {});
            continue;
          }
          Trace("arith-static-pf")
              << "- prove " << b << " from " << ita->second << std::endl;
          // To weaken a bound, we do the following:
          //          ---------- EVALUATE, TRUE_ELIM
          // c >= n1  n1-n2 >= 0
          // ------------------- MACRO_ARITH_SCALE_SUM_UB
          // c + (n1-n2) >= n1
          // ------------------ MACRO_SR_PRED_TRANSFORM
          // (c >= n2) = true
          // where n1, n2 are numeral constants such that n1 >= n2. The same
          // goes for the other relations.
          Node diff = nm->mkNode(Kind::SUB, ita->second[1], b[1]);
          Node diffRel = nm->mkNode(
              ck, diff, nm->mkConstRealOrInt(diff.getType(), Rational(0)));
          Node dreval = evaluate(diffRel, {}, {}, false);
          if (dreval == truen)
          {
            Node dreq = diffRel.eqNode(dreval);
            cdp.addStep(dreq, ProofRule::EVALUATE, {}, {diffRel});
            cdp.addStep(diffRel, ProofRule::TRUE_ELIM, {dreq}, {});
            // by convention, macro sum ub requires negative coefficients for
            // upper bounds
            Node one = nm->mkConstInt(
                Rational((ck == Kind::GEQ || ck == Kind::GT) ? -1 : 1));
            Trace("arith-static-pf")
                << "- add " << ita->second << " with " << diffRel << std::endl;
            std::vector<Node> premises{ita->second, diffRel};
            std::vector<Node> cpre{one, one};
            std::vector<Node> coeff = getMacroSumUbCoeff(nm, premises, cpre);
            ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
            Trace("arith-static-pf")
                << "- check " << premises << " " << coeff << std::endl;
            Node meq = pc->checkDebug(
                ProofRule::MACRO_ARITH_SCALE_SUM_UB, premises, coeff);
            cdp.addStep(
                meq, ProofRule::MACRO_ARITH_SCALE_SUM_UB, premises, coeff);
            Trace("arith-static-pf") << "- got " << meq << std::endl;
            cdp.addStep(eq, ProofRule::MACRO_SR_PRED_TRANSFORM, {meq}, {eq});
            continue;
          }
        }
        Trace("arith-static-pf") << "FAILED to prove branch " << b << std::endl;
        cdp.addTrustedStep(fact, TrustId::ARITH_STATIC_LEARN, {}, {});
        return cdp.getProofFor(fact);
      }
    }
    Node pullc = nm->mkNode(Kind::ITE, conc[0][0], branches[0], branches[1]);
    Node equiv = conc.eqNode(pullc);
    Trace("arith-static-pf") << "- subgoal " << equiv << std::endl;
    cdp.addTrustedStep(equiv, TrustId::ARITH_STATIC_LEARN, {}, {});
    Node trueIte = nm->mkNode(Kind::ITE, conc[0][0], truen, truen);
    Node equiv2 = pullc.eqNode(trueIte);
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(pullc, cargs);
    cdp.addStep(equiv2, cr, congPremises, cargs);
    Node equiv3 = trueIte.eqNode(truen);
    Trace("arith-static-pf") << "- subgoal " << equiv3 << std::endl;
    cdp.addTrustedStep(equiv3, TrustId::ARITH_STATIC_LEARN, {}, {});
    Node concEqTrue = conc.eqNode(truen);
    cdp.addStep(concEqTrue, ProofRule::TRANS, {equiv, equiv2, equiv3}, {});
    cdp.addStep(conc, ProofRule::TRUE_ELIM, {concEqTrue}, {});
  }
  if (!antec.empty())
  {
    cdp.addStep(fact, ProofRule::SCOPE, {conc}, antec);
  }
  return cdp.getProofFor(fact);
}

std::string ArithStaticLearner::identify() const
{
  return "ArithStaticLearner";
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
