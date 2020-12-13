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
#include <set>

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

  //Make assumptions uniform
  std::vector<Node> new_children;
  for(int i=0; i < pfn->getChildren().size(); i++){
    if (static_cast<VeritRule>(std::stoul(pfn->getChildren()[i]->getArguments()[0].toString())) == VeritRule::ASSUME){
      new_children.push_back(nm->mkNode(kind::SEXPR,cl,pfn->getChildren()[i]->getArguments()[2]));
    }
    else{
      new_children.push_back(pfn->getChildren()[i]->getArguments()[2]);
    }
  }

  switch (id)
  {
    case VeritRule::ANCHOR:
    {
      return true;
    }
    case VeritRule::ASSUME:
    {
      return true;
    }
    case VeritRule::ANCHOR_SUBPROOF:
    {  // TODO
      return true;
    }
    case VeritRule::INPUT:
    {  // TODO
      return true;
    }
    case VeritRule::TRUE:
    {
      return (res == nm->mkNode(kind::SEXPR, cl, nm->mkConst(true)));
    }
    case VeritRule::FALSE:
    {
      return (res == nm->mkNode(kind::SEXPR, cl, nm->mkConst(true).negate()));
    }
    case VeritRule::NOT_NOT:
    {
      return (res[0].toString() == cl.toString() && res[1] == res[2].negate().negate().negate());
    }
    case VeritRule::AND_POS:
    {
      // Special case n=1
      if (res[0].toString() == cl.toString() && res[1][0] == res[2] && res[1].getKind() == kind::NOT)
      {
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
      return (res[0].toString() == cl.toString() && equal && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::AND);
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
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::AND && equal && neg);
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
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::OR && equal);
    }
    case VeritRule::OR_NEG:
    {
      // Special case n=1
      if (res[0].toString() == cl.toString() && res[1] == res[2][0])
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
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::OR
          && res[2].getKind() == kind::NOT && equal);
     }
    case VeritRule::XOR_POS1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::XOR && res[1][0][0] == res[2]
          && res[1][0][1] == res[3]);
    }
    case VeritRule::XOR_POS2:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::XOR && res[2].getKind() == kind::NOT
          && res[3].getKind() == kind::NOT && res[1][0][0] == res[2][0]
          && res[1][0][1] == res[3][0]);
    }
    case VeritRule::XOR_NEG1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::XOR
          && res[3].getKind() == kind::NOT && res[1][0] == res[2]
          && res[1][1] == res[3][0]);
    }
    case VeritRule::XOR_NEG2:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::XOR
          && res[2].getKind() == kind::NOT && res[1][0] == res[2][0]
          && res[1][1] == res[3]);
    }
    case VeritRule::IMPLIES_POS:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::IMPLIES
          && res[2].getKind() == kind::NOT && res[1][0][0] == res[2][0]
          && res[1][0][1] == res[3]);
     }
    case VeritRule::IMPLIES_NEG1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::IMPLIES
          && res[1][0] == res[2]);
    }
    case VeritRule::IMPLIES_NEG2:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::IMPLIES
          && res[2].getKind() == kind::NOT && res[1][1] == res[2][0]);
    }
    case VeritRule::EQUIV_POS1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::EQUAL && res[3].getKind() == kind::NOT
          && res[1][0][0] == res[2] && res[1][0][1] == res[3][0]);
    }
    case VeritRule::EQUIV_POS2:
    {
	    std::cout << (res.getKind() == kind::SEXPR) << (res[0].toString() == cl.toString()) << 
(res[1].getKind() == kind::NOT) <<(res[1][0].getKind() == kind::EQUAL) << (res[2].getKind() == kind::NOT)
<<(res[1][0][0] == res[2][0]) << (res[1][0][1] == res[3]);
      return (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::EQUAL && res[2].getKind() == kind::NOT
          && res[1][0][0] == res[2][0] && res[1][0][1] == res[3]);
    }
    case VeritRule::EQUIV_NEG1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && res[1][0] == res[2][0] && res[1][1] == res[3][0]);
    }
    case VeritRule::EQUIV_NEG2:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL && res[1][0] == res[2]
          && res[1][1] == res[3]);
    }
    case VeritRule::ITE_POS1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::ITE && res[1][0][0] == res[2]
          && res[1][0][2] == res[3]);
    }
    case VeritRule::ITE_POS2:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::ITE && res[2].getKind() == kind::NOT
          && res[1][0][0] == res[2][0] && res[1][0][1] == res[3]);
    }
    case VeritRule::ITE_NEG1:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::ITE
          && res[3].getKind() == kind::NOT && res[1][0] == res[2]
          && res[1][2] == res[3][0]);
    }
    case VeritRule::ITE_NEG2:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::ITE
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && res[1][0] == res[2][0] && res[1][1] == res[3][0]);
    }
    case VeritRule::EQ_REFLEXIVE:
    {
      return (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && res[1][0] == res[1][1]);
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
      return (res[0].toString() == cl.toString() && res[n - 1][0] == res[1][0][0]
          && res[n - 1][0][1] == res[n - 2][1]
          && res[n - 1].getKind() == kind::EQUAL && equal);
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
      return (res[0].toString() == cl.toString() && res[n - 1].getKind() == kind::EQUAL
          && res[n - 1][0].getKind() == kind::FUNCTION_TYPE
          && res[n - 1][1].getKind() == kind::FUNCTION_TYPE && equal
          && res[n - 1][0].getOperator() == res[n - 1][1].getOperator());
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
      return (res[0].toString() == cl.toString() && res[n - 1].getKind() == kind::EQUAL
          && res[n - 1][0].getKind() == kind::FUNCTION_TYPE
          && res[n - 1][1].getKind() == kind::FUNCTION_TYPE && equal
          && res[n - 1][0].getOperator() == res[n - 1][0].getOperator());
    }
    /* Leave out rules 28-38 */
    case VeritRule::RESOLUTION:
    {  // TODO
      return true;
    }
    case VeritRule::REFL:
    {  // TODO
	    std::cout << (res[1][0] == res[1][1]) << std::endl;
      return (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL && res[1][0] == res[1][1]);
    }
    case VeritRule::TRANS: //DONE
    {

      Node start;
      Node symm;
      if(new_children[0][1][0] == new_children[1][1][0]){
         start = new_children[0][1][1];
	 symm = new_children[1][1][1];
      }
      else if(new_children[0][1][0] == new_children[1][1][1]){
         start = new_children[0][1][1];
	 symm = new_children[1][1][0];
      }
      else if(new_children[0][1][1] == new_children[1][1][0]){
         start = new_children[0][1][0];
	 symm = new_children[1][1][1];
      }
      else if(new_children[0][1][1] == new_children[1][1][1]){
         start = new_children[0][1][0];
	 symm = new_children[1][1][0];
      }
      else{
        return false;
      }
      if (new_children[0][0].toString() != cl.toString()
          || new_children[0][1].getKind() != kind::EQUAL
	  || new_children[1][0].toString() != cl.toString()
          || new_children[1][1].getKind() != kind::EQUAL)
      {
        return false;
      }

      for (int i = 2; i < new_children.size() - 1; i++)
      {
        if (new_children[i][0].toString() != cl.toString()
            || new_children[i][1].getKind() != kind::EQUAL)
        {
          return false;
        }
        if (new_children[i][1][0] == symm)
        {
          symm = new_children[i][1][1];
        }
	else if (new_children[i][1][1] == symm){
	  symm = new_children[i][1][0];
	}
	else{
	  return false;
	}
      }
      return (res[0].toString() == cl.toString()
      && ((res[1][0] == start && res[1][1] == symm) || (res[1][0] == symm && res[1][1] == start))
      && res[1].getKind() == kind::EQUAL);
     }
    case VeritRule::CONG://DONE
    {
      for (int i = 0; i < new_children.size(); i++)
      {
        if (new_children[i][0].toString() != cl.toString()
            || new_children[i][1].getKind() != kind::EQUAL)
        {

          return false;
        }
        if (!(new_children[i][1][0] == res[1][0][i] && new_children[i][1][1] == res[1][1][i])
	 && !(new_children[i][1][0] == res[1][1][i] && new_children[i][1][1] == res[1][1][i]))
        {
          return false;
        }

      }
      return (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && res[1][0].getKind() == res[1][1].getKind()
          && res[1][0].getOperator() == res[1][1].getOperator());
    }
    case VeritRule::AND:
    {
      bool equal = false;
        for (int i = 0;
             i < (new_children[0][1].end() - new_children[0][1].begin());
             i++)
        {
          if (new_children[0][1][i] == res[1])
          {
            equal = true;
          }
        }
        return (res[0].toString() == cl.toString() && new_children[0][0] == cl
            && new_children[0][1].getKind() == kind::AND && equal);
    }
    case VeritRule::TAUTOLOGIC_CLAUSE:
    {
      bool equal = false;
      for (int i = 0; i < (new_children[0].end() - new_children[0].begin()); i++)
      {
        Node clause = new_children[0][i];
        for (int j = 0; j < (new_children[0].end() - new_children[0].begin()); j++)
        {
          if (new_children[0][i] == new_children[0][i].negate())
          {
            equal = true;
          }
        }
      }
      return (res[0].toString() == cl.toString() && new_children[0][0] == cl
          && res[1] == nm->mkConst(true) && equal);
    }
    case VeritRule::NOT_OR:
    {
      //Special case if the child is an assume
      if (static_cast<VeritRule>(std::stoul(pfn->getChildren()[0]->getArguments()[0].toString())) == VeritRule::ASSUME)
      {
        bool equal = false;
        for (int i = 0; i < (new_children[0][0].end() - new_children[0][0].end()); i++)
        {
          if (new_children[0][0][i] == res[1].negate())
          {
            equal = true;
          }
        }
        return (res[0].toString() == cl.toString()
            && new_children[0].getKind() == kind::NOT
            && new_children[0][0].getKind() == kind::OR && equal);
      }
      //Otherwise
      bool equal = false;
      for (int i = 0;
           i < (new_children[0][1][0].end() - new_children[0][1][0].begin());
           i++)
      {
        if (new_children[0][1][0][i] == res[1].negate())
        {
          equal = true;
        }
      }
      return (res[0].toString() == cl.toString() && new_children[0][0] == cl
          && new_children[0][0].getKind() == kind::NOT
          && new_children[0][0][0].getKind() == kind::OR && equal);
    }
    case VeritRule::OR:
    {
      bool equal;
      if((new_children[0][1].end() - new_children[0][1].begin()) == (res.end()-res.begin())){return false;}
      for (int i = 0; i < (new_children[0][1].end() - new_children[0][1].begin());
           i++)
      {
        if (new_children[0][1][i].toString() == res[i+1].toString())
        {
          equal = true;
        }
      }
      return (res[0].toString() == cl.toString() && new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::OR
          && equal);
    }
    case VeritRule::DUPLICATED_LITERALS:{//TODO: could be better
      std::vector<Node> resVec;
      for (int i = 1; i < (res.end() - res.begin());
           i++)
      {
        resVec.push_back(res[i]);
      }
      std::set<Node> s1(resVec.begin(),resVec.end());
      std::vector<Node> childVec;
      for (int i = 1; i < (new_children[0].end() - new_children[0].begin());
           i++)
      {
        childVec.push_back(new_children[0][i]);
      }
      std::set<Node> s2(childVec.begin(),childVec.end());

      int j = 1;
      for (int i = 1; i < (new_children[0].end() - new_children[0].begin()) && j < (res.end()-res.begin());
           i++)
      {
        if(new_children[0][i] == res[j]){j++;}
      }
      if(j==(new_children[0][1].end() - new_children[0][1].begin())-1 && s1.size() == s2.size()){return true;}
      return false;
    }
    default:
    {
      return true; //TODO: Change to false
    }
  }
}
//Add res.getKind() == kind::SEXPR everywhere
static bool veritProofChecker(std::shared_ptr<ProofNode> pfn)
{
   //std::cout << " CHECK CHILD ";
   //std::cout  << pfn->getResult() << " ";
   //std::cout<<veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())))
   //<< std::endl;
  bool success;

  VeritRule id = static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()));
  Node res = pfn->getArguments()[2];  //Give this as arguments to veritProofChecker
  std::vector<Node> new_children;
  for (std::shared_ptr<ProofNode> child : pfn->getChildren())
  {
    new_children.push_back(child->getArguments()[2]);
  }

  if(checkInternal(pfn)){
    Trace("verit-checker")
        << "... check succeeded " << res << " " << veritRuletoString(id)
        << " " << new_children << std::endl;
  }
  else{
    Trace("verit-checker")
        << "... check failed " << res << " " << veritRuletoString(id) << " "
        << new_children << std::endl;

    Trace("verit-checker-debug")
        << "... check failed " << res << " " << veritRuletoString(id) << " "
        << new_children << std::endl;
    success = false;
  }
  for (auto child : pfn->getChildren())
  {
    veritProofChecker(child);
  }
  return success;
}

}  // namespace proof

}  // namespace CVC4

#endif
