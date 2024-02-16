/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes.
 */

#include "proof/alethe/alethe_printer.h"

#include <iostream>
#include <sstream>
#include <unordered_map>

#include "options/printer_options.h"
#include "proof/alethe/alethe_proof_rule.h"

namespace cvc5::internal {

namespace proof {

LetUpdaterPfCallback::LetUpdaterPfCallback(AletheLetBinding& lbind)
    : d_lbind(lbind)
{
}

LetUpdaterPfCallback::~LetUpdaterPfCallback() {}

bool LetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                        const std::vector<Node>& fa,
                                        bool& continueUpdate)
{
  ProofRule r = pn->getRule();
  if (r == ProofRule::ASSUME)
  {
    d_lbind.process(pn->getResult());
    return false;
  }
  const std::vector<Node>& args = pn->getArguments();
  if (r == ProofRule::SCOPE)
  {
    for (size_t i = 0, size = args.size(); i < size; ++i)
    {
      d_lbind.process(args[i]);
    }
    return false;
  }
  // Letification done on the converted terms (thus from the converted
  // conclusion) and potentially on arguments, which means to ignore the first
  // two arguments (which are the Alethe rule and the original conclusion).
  AlwaysAssert(args.size() > 2)
      << "res: " << pn->getResult() << "\nid: " << pn->getRule();
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    Trace("alethe-printer") << "Process " << args[i] << "\n";
    // We do not go *below* cl, since the clause itself cannot be shared (goes
    // against the Alethe specification). We assume that s-expressions with a
    // bound variable as first argument are all of the form (cl ...).
    if (args[i].getKind() == Kind::SEXPR
        && args[i][0].getKind() == Kind::BOUND_VARIABLE)
    {
      for (const auto& arg : args[i])
      {
        d_lbind.process(arg);
      }
      continue;
    }
    d_lbind.process(args[i]);
  }
  return false;
}

AletheProofPrinter::AletheProofPrinter(Env& env)
    : EnvObj(env),
      d_lbind(options().printer.dagThresh ? options().printer.dagThresh + 1
                                          : 0),
      d_cb(new LetUpdaterPfCallback(d_lbind))
{
}

void AletheProofPrinter::printTerm(std::ostream& out, TNode n)
{
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  // We print lambda applications in non-curried manner
  options::ioutils::applyFlattenHOChains(ss, true);
  options::ioutils::applyDagThresh(ss, 0);
  ss << d_lbind.convert(n, "@p_");
  out << ss.str();
}

void AletheProofPrinter::print(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    const std::map<Node, std::string>& assertionNames)
{
  Trace("alethe-printer") << "- Print proof in Alethe format. " << std::endl;
  // ignore outer scope
  pfn = pfn->getChildren()[0];
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0];
  AlwaysAssert(innerPf);

  if (options().printer.dagThresh)
  {
    // Traverse the proof node to letify the (converted) conclusions of proof
    // steps. Note that we traverse the original proof node because assumptions
    // may apper just in them (if they are not used in the rest of the proof).
    // If that's the case then repeated terms *only* in assumptions would not be
    // letified otherwise.
    ProofNodeUpdater updater(d_env, *(d_cb.get()), false, false);
    Trace("alethe-printer") << "- letify.\n";
    updater.process(pfn);

    std::vector<Node> letList;
    d_lbind.letify(letList);
    if (TraceIsOn("alethe-printer"))
    {
      for (TNode n : letList)
      {
        Trace("alethe-printer")
            << "Term " << n << " has id " << d_lbind.getId(n) << "\n";
      }
    }
  }

  Trace("alethe-printer") << "- Print assumptions.\n";
  std::unordered_map<Node, std::string> assumptions;
  const std::vector<Node>& args = pfn->getArguments();
  // Special handling for the first scope
  // Print assumptions and add them to the list but do not print anchor.
  for (size_t i = 0, size = args.size(); i < size; i++)
  {
    auto it = assertionNames.find(args[i]);
    if (it != assertionNames.end())
    {
      out << "(assume " << it->second << " ";
      assumptions[args[i]] = it->second;
    }
    else
    {  // assumptions are always being declared
      out << "(assume a" << i << " ";
      assumptions[args[i]] = "a" + std::to_string(i);
    }
    printTerm(out, args[i]);
    out << ")\n";
  }
  // Then, print the rest of the proof node
  uint32_t start_t = 1;
  std::unordered_map<std::shared_ptr<ProofNode>, std::string> steps = {};
  printInternal(out, pfn->getChildren()[0], assumptions, steps, "", start_t);
}

std::string AletheProofPrinter::printInternal(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    std::unordered_map<Node, std::string>& assumptions,
    std::unordered_map<std::shared_ptr<ProofNode>, std::string>& steps,
    std::string current_prefix,
    uint32_t& current_step_id)
{
  int step_id = current_step_id;
  const std::vector<Node>& args = pfn->getArguments();

  // Assumptions are printed at the anchor and therefore have to be in the list
  // of assumptions when an assume is reached. Since assumptions are
  // untranslated, it's handled as a special case here.
  if (pfn->getRule() == ProofRule::ASSUME)
  {
    Trace("alethe-printer")
        << "... reached assumption " << pfn->getResult() << std::endl;
    Node res = pfn->getResult();

    auto it = assumptions.find(res);
    Assert(it != assumptions.end()) << "Assumption has not been printed yet! "
                                    << res << "/" << assumptions << std::endl;
    Trace("alethe-printer") << "... found assumption in list " << it->second
                            << ": " << res << "/" << assumptions << std::endl;
    return it->second;
  }

  // Get the alethe proof rule
  AletheRule arule = getAletheRule(args[0]);
  // If the current step is already printed return its id
  auto it = steps.find(pfn);
  if (it != steps.end())
  {
    Trace("alethe-printer")
        << "... step is already printed " << it->second << " "
        << pfn->getResult() << " " << arule << " / " << args << std::endl;
    return it->second;
  }
  std::vector<std::string> current_assumptions;
  std::unordered_map<Node, std::string> assumptions_before_subproof =
      assumptions;
  std::unordered_map<std::shared_ptr<ProofNode>, std::string>
      steps_before_subproof = steps;

  // In case the rule is an anchor it is printed before its children.
  if (arule >= AletheRule::ANCHOR_SUBPROOF && arule <= AletheRule::ANCHOR_SKO_EX)
  {
    // Print anchor
    std::string current_t =
        current_prefix + "t" + std::to_string(current_step_id);
    Trace("alethe-printer")
        << "... print anchor " << pfn->getResult() << " " << arule << " "
        << " / " << args << std::endl;
    out << "(anchor :step " << current_t;

    // Append index of anchor to prefix so that all steps in the subproof use it
    current_prefix.append("t" + std::to_string(current_step_id) + ".");

    // Reset the current step id s.t. the numbering inside the subproof starts
    // with 1
    current_step_id = 1;

    // If the subproof is a bind the arguments need to be printed as
    // assignments, i.e. args=[(= v0 v1)] is printed as (:= (v0 Int) v1).
    //
    // Note that since these are variables there is no need to letify.
    if (arule >= AletheRule::ANCHOR_BIND)
    {
      out << " :args (";
      for (size_t j = 3, size = args.size(); j < size; j++)
      {
        Assert(args[j].getKind() == Kind::EQUAL);
        // if the rhs is a variable, it must be declared first
        if (args[j][1].getKind() == Kind::BOUND_VARIABLE)
        {
          out << "(" << args[j][1] << " " << args[j][1].getType() << ") ";
        }
        out << "(:= " << args[j][0] << " ";
        printTerm(out, args[j][1]);
        out  << ")" << (j != args.size() - 1 ? " " : "");
      }
      out << ")";
    }
    // In all other cases there are no arguments
    out << ")\n";

    // If the subproof is a genuine subproof the arguments are printed as
    // assumptions. To be able to discharge the assumptions afterwards we need
    // to store them.
    if (arule == AletheRule::ANCHOR_SUBPROOF)
    {
      for (size_t i = 3, size = args.size(); i < size; i++)
      {
        std::string assumption_name =
            current_prefix + "a" + std::to_string(i - 3);
        Trace("alethe-printer")
            << "... print assumption " << args[i] << std::endl;
        out << "(assume " << assumption_name << " ";
        printTerm(out, args[i]);
        out << ")\n";
        assumptions[args[i]] = assumption_name;
        current_assumptions.push_back(assumption_name);
      }
    }
  }

  // Print children
  std::vector<std::string> child_prefixes;
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    std::string child_prefix = printInternal(
        out, child, assumptions, steps, current_prefix, current_step_id);
    child_prefixes.push_back(child_prefix);
  }

  // If the rule is a subproof a final subproof step needs to be printed
  if (arule >= AletheRule::ANCHOR_SUBPROOF && arule <= AletheRule::ANCHOR_SKO_EX)
  {
    Trace("alethe-printer") << "... print anchor node " << pfn->getResult()
                            << " " << arule << " / " << args << std::endl;

    current_prefix.pop_back();
    out << "(step " << current_prefix << " ";
    printTerm(out, args[2]);
    out << " :rule " << arule;

    // Reset steps array to the steps before the subproof since steps inside the
    // subproof cannot be accessed anymore
    steps = steps_before_subproof;
    assumptions = assumptions_before_subproof;

    // Add to map of printed steps
    steps[pfn] = current_prefix;
    Trace("alethe-printer") << "... add to steps " << pfn->getArguments()[2]
                            << " " << current_prefix << std::endl;

    // Reset step id to the number before the subproof + 1
    current_step_id = step_id + 1;

    // Discharge assumptions in the case of subproof
    // The assumptions of this level have been stored in current_assumptions
    if (arule == AletheRule::ANCHOR_SUBPROOF)
    {
      out << " :discharge (";
      for (size_t j = 0, size = current_assumptions.size(); j < size; j++)
      {
        out << current_assumptions[j]
            << (j != current_assumptions.size() - 1 ? " " : "");
      }
      out << ")";
    }
    out << ")\n";
    return current_prefix;
  }

  // Otherwise, the step is a normal step
  // Print current step
  std::string current_t =
      current_prefix + "t" + std::to_string(current_step_id);
  Trace("alethe-printer") << "... print node " << current_t << " "
                          << pfn->getResult() << " " << arule << " / " << args
                          << std::endl;

  // Add to map of printed steps
  steps[pfn] = current_t;
  Trace("alethe-printer") << "... add to steps " << pfn->getArguments()[2]
                          << " " << current_t << std::endl;
  current_step_id++;

  out << "(step " << current_t << " ";
  printTerm(out, args[2]);
  out << " :rule " << arule;
  if (pfn->getChildren().size() >= 1)
  {
    out << " :premises (";
    for (size_t i = 0, size = child_prefixes.size(); i < size; i++)
    {
      out << child_prefixes[i] << (i != size - 1? " " : "");
    }
    out << ")";
  }
  if (args.size() > 3)
  {
    out << " :args (";
    for (size_t i = 3, size = args.size(); i < size; i++)
    {
      if (arule == AletheRule::FORALL_INST)
      {
        out << "(:= " << args[i][0] << " ";
        printTerm(out, args[i][1]);
        out << ")";
      }
      else
      {
        printTerm(out, args[i]);
      }
      if (i != args.size() - 1)
      {
        out << " ";
      }
    }
    out << ")";
  }
  out << ")\n";
  return current_t;
}

}  // namespace proof

}  // namespace cvc5::internal
