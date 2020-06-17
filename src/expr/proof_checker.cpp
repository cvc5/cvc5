/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof checker
 **/

#include "expr/proof_checker.h"

#include "expr/skolem_manager.h"
#include "smt/smt_statistics_registry.h"

using namespace CVC4::kind;

namespace CVC4 {

Node ProofRuleChecker::check(PfRule id,
                             const std::vector<Node>& children,
                             const std::vector<Node>& args)
{
  // convert to witness form
  std::vector<Node> childrenw = children;
  std::vector<Node> argsw = args;
  SkolemManager::convertToWitnessFormVec(childrenw);
  SkolemManager::convertToWitnessFormVec(argsw);
  Node res = checkInternal(id, childrenw, argsw);
  // res is in terms of witness form, convert back to Skolem form
  return SkolemManager::getSkolemForm(res);
}

Node ProofRuleChecker::checkChildrenArg(PfRule id,
                                        const std::vector<Node>& children,
                                        Node arg)
{
  return check(id, children, {arg});
}
Node ProofRuleChecker::checkChildren(PfRule id,
                                     const std::vector<Node>& children)
{
  return check(id, children, {});
}
Node ProofRuleChecker::checkChild(PfRule id, Node child)
{
  return check(id, {child}, {});
}
Node ProofRuleChecker::checkArg(PfRule id, Node arg)
{
  return check(id, {}, {arg});
}

Node ProofRuleChecker::mkAnd(const std::vector<Node>& a)
{
  if (a.empty())
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (a.size() == 1)
  {
    return a[0];
  }
  return NodeManager::currentNM()->mkNode(AND, a);
}

bool ProofRuleChecker::getUInt32(TNode n, uint32_t& i)
{
  // must be a non-negative integer constant that fits an unsigned int
  if (n.isConst() && n.getType().isInteger()
      && n.getConst<Rational>().sgn() >= 0
      && n.getConst<Rational>().getNumerator().fitsUnsignedInt())
  {
    i = n.getConst<Rational>().getNumerator().toUnsignedInt();
    return true;
  }
  return false;
}

bool ProofRuleChecker::getBool(TNode n, bool& b)
{
  if (n.isConst() && n.getType().isBoolean())
  {
    b = n.getConst<bool>();
    return true;
  }
  return false;
}

ProofCheckerStatistics::ProofCheckerStatistics()
    : d_ruleChecks("ProofCheckerStatistics::ruleChecks"),
    d_totalRuleChecks("ProofCheckerStatistics::totalRuleChecks", 0)
{
  smtStatisticsRegistry()->registerStat(&d_ruleChecks);
  smtStatisticsRegistry()->registerStat(&d_totalRuleChecks);
}

ProofCheckerStatistics::~ProofCheckerStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_ruleChecks);
  smtStatisticsRegistry()->unregisterStat(&d_totalRuleChecks);
}

Node ProofChecker::check(ProofNode* pn, Node expected)
{
  return check(pn->getRule(), pn->getChildren(), pn->getArguments(), expected);
}

Node ProofChecker::check(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  // optimization: immediately return for ASSUME
  if (id == PfRule::ASSUME)
  {
    Assert(children.empty());
    Assert(args.size() == 1 && args[0].getType().isBoolean());
    Assert(expected.isNull() || expected == args[0]);
    return expected;
  }
  // record stat
  d_stats.d_ruleChecks << id;
  ++d_stats.d_totalRuleChecks;
  Trace("pfcheck") << "ProofChecker::check: " << id << std::endl;
  std::vector<Node> cchildren;
  for (const std::shared_ptr<ProofNode>& pc : children)
  {
    Assert(pc != nullptr);
    Node cres = pc->getResult();
    if (cres.isNull())
    {
      Trace("pfcheck") << "ProofChecker::check: failed child" << std::endl;
      Unreachable()
          << "ProofChecker::check: child proof was invalid (null conclusion)"
          << std::endl;
      // should not have been able to create such a proof node
      return Node::null();
    }
    cchildren.push_back(cres);
    if (Trace.isOn("pfcheck"))
    {
      std::stringstream ssc;
      pc->printDebug(ssc);
      Trace("pfcheck") << "     child: " << ssc.str() << " : " << cres
                       << std::endl;
    }
  }
  Trace("pfcheck") << "      args: " << args << std::endl;
  Trace("pfcheck") << "  expected: " << expected << std::endl;
  std::stringstream out;
  // we use trusted (null) checkers here, since we want the proof generation to
  // proceed without failing here.
  Node res = checkInternal(id, cchildren, args, expected, out, true);
  if (res.isNull())
  {
    Trace("pfcheck") << "ProofChecker::check: failed" << std::endl;
    Unreachable() << "ProofChecker::check: failed, " << out.str() << std::endl;
    // it did not match the given expectation, fail
    return Node::null();
  }
  Trace("pfcheck") << "ProofChecker::check: success!" << std::endl;
  return res;
}

Node ProofChecker::checkDebug(PfRule id,
                              const std::vector<Node>& cchildren,
                              const std::vector<Node>& args,
                              Node expected,
                              const char* traceTag)
{
  std::stringstream out;
  // since we are debugging, we want to treat trusted (null) checkers as
  // a failure.
  Node res = checkInternal(id, cchildren, args, expected, out, false);
  Trace(traceTag) << "ProofChecker::checkDebug: " << id;
  if (res.isNull())
  {
    Trace(traceTag) << " failed, " << out.str() << std::endl;
  }
  else
  {
    Trace(traceTag) << " success" << std::endl;
  }
  Trace(traceTag) << "cchildren: " << cchildren << std::endl;
  Trace(traceTag) << "     args: " << args << std::endl;
  return res;
}

Node ProofChecker::checkInternal(PfRule id,
                                 const std::vector<Node>& cchildren,
                                 const std::vector<Node>& args,
                                 Node expected,
                                 std::stringstream& out,
                                 bool useTrustedChecker)
{
  std::map<PfRule, ProofRuleChecker*>::iterator it = d_checker.find(id);
  if (it == d_checker.end())
  {
    // no checker for the rule
    out << "no checker for rule " << id << std::endl;
    return Node::null();
  }
  else if (it->second == nullptr)
  {
    if (useTrustedChecker)
    {
      Notice() << "ProofChecker::check: trusting PfRule " << id << std::endl;
      // trusted checker
      return expected;
    }
    else
    {
      out << "trusted checker for rule " << id << std::endl;
      return Node::null();
    }
  }
  // check it with the corresponding checker
  Node res = it->second->check(id, cchildren, args);
  if (!expected.isNull())
  {
    Node expectedw = expected;
    if (res != expectedw)
    {
      out << "result does not match expected value." << std::endl
          << "    PfRule: " << id << std::endl;
      for (const Node& c : cchildren)
      {
        out << "     child: " << c << std::endl;
      }
      for (const Node& a : args)
      {
        out << "       arg: " << a << std::endl;
      }
      out << "    result: " << res << std::endl
          << "  expected: " << expected << std::endl;
      // it did not match the given expectation, fail
      return Node::null();
    }
  }
  return res;
}

void ProofChecker::registerChecker(PfRule id, ProofRuleChecker* psc)
{
  std::map<PfRule, ProofRuleChecker*>::iterator it = d_checker.find(id);
  if (it != d_checker.end())
  {
    // checker is already provided
    Notice() << "ProofChecker::registerChecker: checker already exists for "
             << id << std::endl;
    return;
  }
  d_checker[id] = psc;
}

}  // namespace CVC4
