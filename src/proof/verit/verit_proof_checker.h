/*********************                                                        */
/*! \file verit_proof_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing veriT proof nodes
 **/

#include <iostream>
#include <memory>
#include <string>

#include "cvc4_private.h"
#include "expr/proof_node_updater.h"
#include "proof/verit/verit_proof_rule.cpp"

#ifndef CVC4__PROOF__VERIT_PROOF_CHECKER_H
#define CVC4__PROOF__VERIT_PROOF_CHECKER_H
namespace CVC4 {

namespace proof {

static bool checkInternal(std::shared_ptr<ProofNode> pfn)
{
  VeritRule id =
      static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()));

  if (id == VeritRule::ANCHOR_SUBPROOF)
  {
    return true;
  }

  Node res = pfn->getArguments()[2];
  NodeManager* nm = NodeManager::currentNM();
  Node cl = nm->mkBoundVar("cl", nm->stringType());

  std::vector<Node> new_children;
  for (std::shared_ptr<ProofNode> child : pfn->getChildren())
  {
    new_children.push_back(child->getArguments()[2]);
  }

  switch (id)
  {
    case VeritRule::ANCHOR:
    {
      Trace("verit-checker")
          << "... check succeeded " << res << " " << veritRuletoString(id)
          << " " << new_children << std::endl;
      return true;
    }
    case VeritRule::ASSUME:
    {
      Trace("verit-checker")
          << "... check succeeded " << res << " " << veritRuletoString(id)
          << " " << new_children << std::endl;
      return true;
    }
    case VeritRule::ANCHOR_SUBPROOF:
    {  // TODO
      Trace("verit-checker")
          << "... check succeeded " << res << " " << veritRuletoString(id)
          << " " << new_children << std::endl;
      return true;
    }
    case VeritRule::INPUT:
    {  // TODO
      Trace("verit-checker")
          << "... check succeeded " << res << " " << veritRuletoString(id)
          << " " << new_children << std::endl;
      return true;
    }
    case VeritRule::TRUE:
    {
      if (res == nm->mkNode(kind::SEXPR, cl, nm->mkConst(true)))
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::FALSE:
    {
      if (res == nm->mkNode(kind::SEXPR, cl, nm->mkConst(true).negate()))
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::NOT_NOT:
    {
      if (res[0] == cl && res[1] == res[2].negate().negate().negate())
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::AND_POS:
    {
      // Special case n=1
      if (res[0] == cl && res[1][0] == res[2] && res[1].getKind() == kind::NOT)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
      // Otherwise
      bool equal = false;
      for (auto i = res[1][0].begin(); i != res[1][0].end(); i++)
      {
        if (*i == res[2])
        {
          equal = true;
        }
      }
      if (res[0] == cl && equal && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::AND)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::AND_NEG:
    {
      bool equal = true;
      bool neg = true;
      for (auto i = 0; i < res[1].end() - res[1].end(); i++)
      {
        if (res[1][i] != res[i + 2][0])
        {
          equal = false;
        }
        if (res[i + 2].getKind() != kind::NOT)
        {
          neg = false;
        }
      }
      if (res[0] == cl && res[1].getKind() == kind::AND && equal && neg)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::OR_POS:
    {
      bool equal = true;
      for (auto i = 0; i < res[1][0].end() - res[1][0].end(); i++)
      {
        if (res[1][0][i] != res[i + 2])
        {
          equal = false;
        }
      }
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::OR && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::OR_NEG:
    {
      // Special case n=1
      if (res[0] == cl && res[1] == res[2][0])
      {
        return true;
      }
      // Otherwise
      bool equal = false;
      for (auto i = res[1].begin(); i != res[1].end(); i++)
      {
        if (*i == res[2][0])
        {
          equal = true;
        }
      }
      if (res[0] == cl && res[1].getKind() == kind::OR
          && res[2].getKind() == kind::NOT && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::XOR_POS1:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::XOR && res[1][0][0] == res[2]
          && res[1][0][1] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::XOR_POS2:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::XOR && res[2].getKind() == kind::NOT
          && res[3].getKind() == kind::NOT && res[1][0][0] == res[2][0]
          && res[1][0][1] == res[3][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::XOR_NEG1:
    {
      if (res[0] == cl && res[1].getKind() == kind::XOR
          && res[3].getKind() == kind::NOT && res[1][0] == res[2]
          && res[1][1] == res[3][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::XOR_NEG2:
    {
      if (res[0] == cl && res[1].getKind() == kind::XOR
          && res[2].getKind() == kind::NOT && res[1][0] == res[2][0]
          && res[1][1] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::IMPLIES_POS:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::IMPLIES
          && res[2].getKind() == kind::NOT && res[1][0][0] == res[2][0]
          && res[1][0][1] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::IMPLIES_NEG1:
    {
      if (res[0] == cl && res[1].getKind() == kind::IMPLIES
          && res[1][0] == res[2])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::IMPLIES_NEG2:
    {
      if (res[0] == cl && res[1].getKind() == kind::IMPLIES
          && res[2].getKind() == kind::NOT && res[1][1] == res[2][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQUIV_POS1:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::EQUAL && res[3].getKind() == kind::NOT
          && res[1][0][0] == res[2] && res[1][0][1] == res[3][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQUIV_POS2:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::EQUAL && res[2].getKind() == kind::NOT
          && res[1][0][0] == res[2][0] && res[1][0][1] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQUIV_NEG1:
    {
      if (res[0] == cl && res[1].getKind() == kind::EQUAL
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && res[1][0] == res[2][0] && res[1][1] == res[3][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQUIV_NEG2:
    {
      if (res[0] == cl && res[1].getKind() == kind::EQUAL && res[1][0] == res[2]
          && res[1][1] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::ITE_POS1:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::ITE && res[1][0][0] == res[2]
          && res[1][0][2] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::ITE_POS2:
    {
      if (res[0] == cl && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::ITE && res[2].getKind() == kind::NOT
          && res[1][0][0] == res[2][0] && res[1][0][1] == res[3])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }

    case VeritRule::ITE_NEG1:
    {
      if (res[0] == cl && res[1].getKind() == kind::ITE
          && res[3].getKind() == kind::NOT && res[1][0] == res[2]
          && res[1][2] == res[3][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::ITE_NEG2:
    {
      if (res[0] == cl && res[1].getKind() == kind::ITE
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && res[1][0] == res[2][0] && res[1][1] == res[3][0])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQ_REFLEXIVE:
    {
      if (res[0] == cl && res[1].getKind() == kind::EQUAL
          && res[1][0] == res[1][1])
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQ_TRANSITIVE:
    {
      bool equal;
      int n = res.end() - res.begin();
      for (auto i = 1; i < n - 1; i++)
      {
        if (res[i][0][1] != res[i + 1][0][0] || res[i].getKind() != kind::NOT
            || res[i][0].getKind() != kind::EQUAL)
        {
          equal = false;
        }
      }
      if (res[0] == cl && res[n - 1][0] == res[1][0][0]
          && res[n - 1][0][1] == res[n - 2][1]
          && res[n - 1].getKind() == kind::EQUAL && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQ_CONGRUENT:
    {  // TODO: I don't need enough about functions
      bool equal;
      int n = res.end() - res.begin();
      for (auto i = 1; i < n - 1; i++)
      {
        if (res[i][0][0] != res[n - 1][0][0][i]
            || res[i][0][1] != res[n - 1][1][0][i]
            || res[i].getKind() != kind::NOT
            || res[i][0].getKind() != kind::EQUAL)
        {
          equal = false;
        }
      }
      std::cout << "delete later " << res[n - 1][0].getOperator() << std::endl;
      if (res[0] == cl && res[n - 1].getKind() == kind::EQUAL
          && res[n - 1][0].getKind() == kind::FUNCTION_TYPE
          && res[n - 1][1].getKind() == kind::FUNCTION_TYPE && equal
          && res[n - 1][0].getOperator() == res[n - 1][1].getOperator())
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::EQ_CONGRUENT_PRED:
    {  // TODO: What is the PREDICATE_TYPE
      bool equal;
      int n = res.end() - res.begin();
      for (auto i = 1; i < n - 1; i++)
      {
        if (res[i][0][0] != res[n - 1][0][0][i]
            || res[i][0][1] != res[n - 1][1][0][i]
            || res[i].getKind() != kind::NOT
            || res[i][0].getKind() != kind::EQUAL)
        {
          equal = false;
        }
      }
      if (res[0] == cl && res[n - 1].getKind() == kind::EQUAL
          && res[n - 1][0].getKind() == kind::FUNCTION_TYPE
          && res[n - 1][1].getKind() == kind::FUNCTION_TYPE && equal
          && res[n - 1][0].getOperator() == res[n - 1][0].getOperator())
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    /* Leave out rules 28-38 */
    case VeritRule::RESOLUTION:
    {  // TODO
      Trace("verit-checker")
          << "... check succeeded " << res << " " << veritRuletoString(id)
          << " " << new_children << std::endl;
      return true;
    }
    case VeritRule::REFL:
    {  // TODO
      if (res[0] == cl && res[1].getKind() == kind::EQUAL)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::TRANS:
    {
      bool equal;
      for (int i = 0; i < new_children.size() - 1; i++)
      {
        if (new_children[i][0] != cl
            || new_children[i][1].getKind() != kind::EQUAL)
        {
          equal = false;
        }
        if (new_children[i][1][1] != new_children[i + 1][1][0])
        {
          equal = false;
        }
      }
      if (res[0] == cl && res[1][0] == new_children[0][0][0]
          && res[1][1] == new_children[new_children.size() - 1][0][1]
          && res[1].getKind() == kind::EQUAL && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::CONG:
    {
      bool equal;
      for (int i = 0; i < new_children.size() - 1; i++)
      {
        if (new_children[i][0] != cl
            || new_children[i][1].getKind() != kind::EQUAL)
        {
          equal = false;
        }
        if (new_children[i][1][0] != res[0][0][i])
        {
          equal = false;
        }
        if (new_children[i][1][1] != res[1][0][i])
        {
          equal = false;
        }
      }
      if (res[0] == cl && res[1].getKind() == kind::EQUAL
          && res[1][0].getKind() == kind::FUNCTION_TYPE
          && res[1][1].getKind() == kind::FUNCTION_TYPE
          && res[1][0].getOperator() == res[1][1].getOperator() && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::AND:
    {
      bool equal = false;
      // In the case that the child is an assume it is not wrapped in an cl
      if (static_cast<VeritRule>(
              std::stoul(pfn->getChildren()[0]->getArguments()[0].toString()))
          == VeritRule::ASSUME)
      {
        for (int i = 0; i < (new_children[0].end() - new_children[0].end());
             i++)
        {
          if (new_children[0][i] == res[1])
          {
            equal = true;
          }
        }
        if (res[0] == cl && new_children[0].getKind() == kind::AND && equal)
        {
          Trace("verit-checker")
              << "... check succeeded " << res << " " << veritRuletoString(id)
              << " " << new_children << std::endl;
          return true;
        }
      }
      else
      {
        for (int i = 0;
             i < (new_children[0][1].end() - new_children[0][1].end());
             i++)
        {
          if (new_children[0][1][i] == res[1])
          {
            equal = true;
          }
        }
        if (res[0] == cl && new_children[0][0] == cl
            && new_children[0][1].getKind() == kind::AND && equal)
        {
          Trace("verit-checker")
              << "... check succeeded " << res << " " << veritRuletoString(id)
              << " " << new_children << std::endl;
          return true;
        }
      }
    }
    case VeritRule::TAUTOLOGIC_CLAUSE:
    {
      bool equal = false;
      for (int i = 0; i < (new_children[0].end() - new_children[0].end()); i++)
      {
        Node clause = new_children[0][i];
        for (int j = 0; j < (new_children[0].end() - new_children[0].end());
             j++)
        {
          if (new_children[0][i] == new_children[0][i].negate())
          {
            equal = true;
          }
        }
      }
      if (res[0] == cl && new_children[0][0] == cl
          && res[1] == nm->mkConst(true) && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::NOT_OR:
    {
      bool equal = false;
      for (int i = 0;
           i < (new_children[0][1][0].end() - new_children[0][1][0].end());
           i++)
      {
        if (new_children[0][1][0][i].negate() == res[1])
        {
          equal = true;
        }
      }
      if (res[0] == cl && new_children[0][0] == cl
          && new_children[0][0].getKind() == kind::NOT
          && new_children[0][0][0].getKind() == kind::OR && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }
    case VeritRule::OR:
    {  // TODO
      bool equal;
      for (int i = 0; i < (new_children[0][1].end() - new_children[0][1].end());
           i++)
      {
        if (new_children[0][i] == res[i])
        {
          equal = true;
        }
      }
      if (res[0] == cl && new_children[0][0] == cl
          && new_children[0][0].getKind() == kind::NOT
          && new_children[0][0][0].getKind() == kind::OR && equal)
      {
        Trace("verit-checker")
            << "... check succeeded " << res << " " << veritRuletoString(id)
            << " " << new_children << std::endl;
        return true;
      }
    }

    default:
    {
      Trace("verit-checker")
          << "... check failed " << res << " " << veritRuletoString(id) << " "
          << new_children << std::endl;
      return false;
    }
  }
}

static bool veritProofChecker(std::shared_ptr<ProofNode> pfn)
{
  // std::cout << " CHECK CHILD " << pfn->getResult() << " "
  // <<veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())))
  // << std::endl;
  checkInternal(pfn);
  for (auto child : pfn->getChildren())
  {
    veritProofChecker(child);
  }
  return true;
}

}  // namespace proof

}  // namespace CVC4

#endif
