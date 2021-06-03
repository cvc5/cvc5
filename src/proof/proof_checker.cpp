/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof checker.
 */

#include "proof/proof_checker.h"

#include "expr/skolem_manager.h"
#include "options/proof_options.h"
#include "proof/proof_node.h"
#include "smt/smt_statistics_registry.h"
#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {

Node ProofRuleChecker::check(PfRule id,
                             const std::vector<Node>& children,
                             const std::vector<Node>& args)
{
  // call instance-specific checkInternal method
  return checkInternal(id, children, args);
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

bool ProofRuleChecker::getKind(TNode n, Kind& k)
{
  uint32_t i;
  if (!getUInt32(n, i))
  {
    return false;
  }
  k = static_cast<Kind>(i);
  return true;
}

Node ProofRuleChecker::mkKindNode(Kind k)
{
  if (k == UNDEFINED_KIND)
  {
    // UNDEFINED_KIND is negative, hence return null to avoid cast
    return Node::null();
  }
  return NodeManager::currentNM()->mkConst(Rational(static_cast<uint32_t>(k)));
}

ProofCheckerStatistics::ProofCheckerStatistics()
    : d_ruleChecks(smtStatisticsRegistry().registerHistogram<PfRule>(
          "ProofCheckerStatistics::ruleChecks")),
      d_totalRuleChecks(smtStatisticsRegistry().registerInt(
          "ProofCheckerStatistics::totalRuleChecks"))
{
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
  // proceed without failing here. We always enable output since a failure
  // implies that we will exit with the error message below.
  Node res = checkInternal(id, cchildren, args, expected, out, true, true);
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
  bool traceEnabled = Trace.isOn(traceTag);
  // Since we are debugging, we want to treat trusted (null) checkers as
  // a failure. We only enable output if the trace is enabled for efficiency.
  Node res =
      checkInternal(id, cchildren, args, expected, out, false, traceEnabled);
  if (traceEnabled)
  {
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
  }
  return res;
}

Node ProofChecker::checkInternal(PfRule id,
                                 const std::vector<Node>& cchildren,
                                 const std::vector<Node>& args,
                                 Node expected,
                                 std::stringstream& out,
                                 bool useTrustedChecker,
                                 bool enableOutput)
{
  std::map<PfRule, ProofRuleChecker*>::iterator it = d_checker.find(id);
  if (it == d_checker.end())
  {
    // no checker for the rule
    if (enableOutput)
    {
      out << "no checker for rule " << id << std::endl;
    }
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
      if (enableOutput)
      {
        out << "trusted checker for rule " << id << std::endl;
      }
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
      if (enableOutput)
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
      }
      // it did not match the given expectation, fail
      return Node::null();
    }
  }
  // fails if pedantic level is not met
  if (options::proofEagerChecking())
  {
    std::stringstream serr;
    if (isPedanticFailure(id, serr, enableOutput))
    {
      if (enableOutput)
      {
        out << serr.str() << std::endl;
        if (Trace.isOn("proof-pedantic"))
        {
          Trace("proof-pedantic")
              << "Failed pedantic check for " << id << std::endl;
          Trace("proof-pedantic") << "Expected: " << expected << std::endl;
          out << "Expected: " << expected << std::endl;
        }
      }
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

void ProofChecker::registerTrustedChecker(PfRule id,
                                          ProofRuleChecker* psc,
                                          uint32_t plevel)
{
  AlwaysAssert(plevel <= 10) << "ProofChecker::registerTrustedChecker: "
                                "pedantic level must be 0-10, got "
                             << plevel << " for " << id;
  registerChecker(id, psc);
  // overwrites if already there
  if (d_plevel.find(id) != d_plevel.end())
  {
    Notice() << "ProofChecker::registerTrustedRule: already provided pedantic "
                "level for "
             << id << std::endl;
  }
  d_plevel[id] = plevel;
}

ProofRuleChecker* ProofChecker::getCheckerFor(PfRule id)
{
  std::map<PfRule, ProofRuleChecker*>::const_iterator it = d_checker.find(id);
  if (it == d_checker.end())
  {
    return nullptr;
  }
  return it->second;
}

uint32_t ProofChecker::getPedanticLevel(PfRule id) const
{
  std::map<PfRule, uint32_t>::const_iterator itp = d_plevel.find(id);
  if (itp != d_plevel.end())
  {
    return itp->second;
  }
  return 0;
}

bool ProofChecker::isPedanticFailure(PfRule id,
                                     std::ostream& out,
                                     bool enableOutput) const
{
  if (d_pclevel == 0)
  {
    return false;
  }
  std::map<PfRule, uint32_t>::const_iterator itp = d_plevel.find(id);
  if (itp != d_plevel.end())
  {
    if (itp->second <= d_pclevel)
    {
      if (enableOutput)
      {
        out << "pedantic level for " << id << " not met (rule level is "
            << itp->second << " which is at or below the pedantic level "
            << d_pclevel << ")";
        bool pedanticTraceEnabled = Trace.isOn("proof-pedantic");
        if (!pedanticTraceEnabled)
        {
          out << ", use -t proof-pedantic for details";
        }
      }
      return true;
    }
  }
  return false;
}

}  // namespace cvc5
