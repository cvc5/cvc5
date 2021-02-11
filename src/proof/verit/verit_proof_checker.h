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
#include <set>
#include <string>
#include <optional>

#include "cvc4_private.h"
#include "expr/proof_node_updater.h"
#include "proof/verit/verit_proof_rule.cpp"

#ifndef CVC4__PROOF__VERIT_PROOF_CHECKER_H
#define CVC4__PROOF__VERIT_PROOF_CHECKER_H
namespace CVC4 {

namespace proof {

enum class CheckResult {
False,
True,
NotTranslated,
NoCheck
};

static bool equalNodes(Node vp1, Node vp2){
  if(vp1.getKind() != vp2.getKind()){
     return false;
  }
  else if(vp1 == vp2){
    return true;
  }
  else if(vp1.getKind() == kind::EQUAL){
     return (equalNodes(vp1[0],vp2[1]) && equalNodes(vp1[1],vp2[0]))
	     || (equalNodes(vp1[0],vp2[0]) && equalNodes(vp1[1],vp2[1]));
  }
  std::vector<Node> vp1s(vp1.begin(),vp1.end());
  std::vector<Node> vp2s(vp2.begin(),vp2.end());
  if(vp1s.size() != vp2s.size()) {return false;}
  bool equal = true;
  for(int i=0; i < vp1s.size();i++){
    equal &= equalNodes(vp1s[i],vp2s[i]);
  }
  return equal;
}

static CheckResult checkStep(std::shared_ptr<ProofNode> pfn)
{
  VeritRule id =
      static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()));
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
    case VeritRule::ANCHOR://DONE
    {
      return CheckResult::NoCheck;
    }
    case VeritRule::ASSUME://DONE
    {
      if (res.end() - res.begin() > 0 && res[0].toString() == cl.toString())
      {
        std::cout << "assume failed " << res << std::endl;
        return CheckResult::False;
      }
      return CheckResult::True;
    }
    case VeritRule::ANCHOR_SUBPROOF://DONE
    {
      return CheckResult::NoCheck;
    }
    case VeritRule::INPUT://DONE
    {
      return CheckResult::NoCheck;
    }
    case VeritRule::TRUE://DONE
    {
      if (equalNodes(res, nm->mkNode(kind::SEXPR, cl, nm->mkConst(true))))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::FALSE://DONE
    {
      if (equalNodes(
              res, nm->mkNode(kind::SEXPR, cl, nm->mkConst(false).negate())))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_NOT://DONE
    {
      if (res[0].toString() == cl.toString()
          && equalNodes(res[1], res[2].notNode().notNode().notNode()))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::AND_POS://DONE
    {
      // Special case n=1
      if (res[0].toString() == cl.toString()
          && equalNodes(res[1][0], res[2])
          && res[1].getKind() == kind::NOT)
      {
        return CheckResult::True;
      }
      // Otherwise
      bool equal = false;
      for (auto i = res[1][0].begin(); i != res[1][0].end(); i++)
      {
        if (equalNodes(*i, res[2]))
        {
          equal = true;
        }
      }
      if (res[0].toString() == cl.toString() && equal && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::AND) {return CheckResult::True;};
      return CheckResult::False;
    }
    case VeritRule::AND_NEG://DONE
    {
      bool equal = true;
      bool neg = true;
      for (auto i = 0; i < res[1].end() - res[1].begin(); i++)
      {
        if (!equalNodes(res[1][i], res[i + 2][0]))
        {
          equal = false;
        }
        if (res[i + 2].getKind() != kind::NOT)
        {
          neg = false;
        }
      }
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::AND && equal && neg){return CheckResult::True;}
      return CheckResult::False;
    }
    case VeritRule::OR_POS://DONE
    {
      bool equal = true;
      for (auto i = 0; i < res[1][0].end() - res[1][0].begin(); i++)
      {
        if (!equalNodes(res[1][0][i], res[i + 2]))
        {
          equal = false;
        }
      }
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::OR && equal){return CheckResult::True;}
      return CheckResult::False;
    }
    case VeritRule::OR_NEG://DONE
    {
      // Special case n=1
      if (res[0].toString() == cl.toString()
          && equalNodes(res[1], res[2][0])
          && res[2].getKind() == kind::NOT)
      {
        return CheckResult::True;
      }
      // Otherwise
      bool equal = false;
      for (auto i = res[1].begin(); i != res[1].end(); i++)
      {
        if (equalNodes(*i, res[2][0]))
        {
          equal = true;
        }
      }
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::OR
          && res[2].getKind() == kind::NOT && equal){return CheckResult::True;}
      return CheckResult::False;
     }
    case VeritRule::XOR_POS1://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::XOR
          && equalNodes(res[1][0][0], res[2])
          && equalNodes(res[1][0][1], res[3]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::XOR_POS2://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::XOR && res[2].getKind() == kind::NOT
          && res[3].getKind() == kind::NOT
          && equalNodes(res[1][0][0], res[2][0])
          && equalNodes(res[1][0][1], res[3][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::XOR_NEG1://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::XOR
          && res[3].getKind() == kind::NOT && equalNodes(res[1][0], res[2])
          && equalNodes(res[1][1], res[3][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::XOR_NEG2://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::XOR
          && res[2].getKind() == kind::NOT
          && equalNodes(res[1][0], res[2][0])
          && equalNodes(res[1][1], res[3]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::IMPLIES_POS://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::IMPLIES
          && res[2].getKind() == kind::NOT
          && equalNodes(res[1][0][0], res[2][0])
          && equalNodes(res[1][0][1], res[3]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
     }
    case VeritRule::IMPLIES_NEG1://DONE
    {
      if (res[0].toString() == cl.toString()
          && res[1].getKind() == kind::IMPLIES
          && equalNodes(res[1][0], res[2]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::IMPLIES_NEG2://DONE
    {
      if (res[0].toString() == cl.toString()
          && res[1].getKind() == kind::IMPLIES && res[2].getKind() == kind::NOT
          && equalNodes(res[1][1], res[2][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQUIV_POS1://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::EQUAL && res[3].getKind() == kind::NOT
          && equalNodes(res[1][0][0], res[2])
          && equalNodes(res[1][0][1], res[3][0]))
      {
        return CheckResult::True;
      }
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::EQUAL && res[3].getKind() == kind::NOT
          && equalNodes(res[1][0][1], res[2])
          && equalNodes(res[1][0][0], res[3][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQUIV_POS2://DONE
    {
      if (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString()
          && res[1].getKind() == kind::NOT && res[1][0].getKind() == kind::EQUAL
          && res[2].getKind() == kind::NOT
          && equalNodes(res[1][0][0], res[2][0])
          && equalNodes(res[1][0][1], res[3]))
      {
        return CheckResult::True;
      }
      if (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString()
          && res[1].getKind() == kind::NOT && res[1][0].getKind() == kind::EQUAL
          && res[2].getKind() == kind::NOT
          && equalNodes(res[1][0][1], res[2][0])
          && equalNodes(res[1][0][0], res[3]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQUIV_NEG1://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && equalNodes(res[1][0], res[2][0])
          && equalNodes(res[1][1], res[3][0]))
      {
        return CheckResult::True;
      }
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && equalNodes(res[1][1], res[2][0])
          && equalNodes(res[1][0], res[3][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQUIV_NEG2://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && equalNodes(res[1][0], res[2])
          && equalNodes(res[1][1], res[3]))
      {
        return CheckResult::True;
      }
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL && res[1][1] == res[2]
          && res[1][0] == res[3]){return CheckResult::True;}
      return CheckResult::False;
    }
    case VeritRule::ITE_POS1://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::ITE
          && equalNodes(res[1][0][0], res[2])
          && equalNodes(res[1][0][2], res[3]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::ITE_POS2://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::NOT
          && res[1][0].getKind() == kind::ITE && res[2].getKind() == kind::NOT
          && equalNodes(res[1][0][0], res[2][0])
          && equalNodes(res[1][0][1], res[3]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::ITE_NEG1://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::ITE
          && res[3].getKind() == kind::NOT && equalNodes(res[1][0], res[2])
          && equalNodes(res[1][2], res[3][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::ITE_NEG2://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::ITE
          && res[2].getKind() == kind::NOT && res[3].getKind() == kind::NOT
          && equalNodes(res[1][0], res[2][0])
          && equalNodes(res[1][1], res[3][0]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQ_REFLEXIVE://DONE
    {
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::EQUAL
          && equalNodes(res[1][0], res[1][1]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQ_TRANSITIVE://DONE
    {
      std::vector<Node> ts;
      ts.push_back(res[1][0][0]);
      ts.push_back(res[1][0][1]);

      bool equal;
      int n = res.end() - res.begin();
      for (auto i = 2; i < n - 1; i++)
      {
	if(std::find(ts.begin(),ts.end(),res[i][0][0]) != ts.end()){
	  ts.push_back(res[i][0][0]);
	}
	else{
          ts.erase(std::find(ts.begin(),ts.end(),res[i][0][0]));
	}
	if(std::find(ts.begin(),ts.end(),res[i][0][1]) != ts.end()){
	  ts.push_back(res[i][0][1]);
	}
	else{
          ts.erase(std::find(ts.begin(),ts.end(),res[i][0][1]));
	}
        if (ts.size() == 2 || res[i].getKind() != kind::NOT
            || res[i][0].getKind() != kind::EQUAL)
        {
          equal = false;
        }
      }
      if (res[0].toString() == cl.toString()
          && equalNodes(res[n - 1][0], ts[0])
          && equalNodes(res[n - 1][1], ts[1])
          && res[n - 1].getKind() == kind::EQUAL && equal)
      {
        return CheckResult::True;
      }
      return CheckResult::False;
     }
    case VeritRule::EQ_CONGRUENT://No symm handling
    {  // TODO: I don't know enough about functions
      bool equal;
      int n = res.end() - res.begin();
      for (auto i = 1; i < n - 1; i++)
      {
        if (!equalNodes(res[i][0][0], res[n - 1][0][0][i])
            || !equalNodes(res[i][0][1], res[n - 1][1][0][i])
            || res[i].getKind() != kind::NOT
            || res[i][0].getKind() != kind::EQUAL)
        {
          equal = false;
        }
      }
      std::cout << "delete later " << res[n - 1][0].getOperator() << std::endl;
      if (res[0].toString() == cl.toString() && res[n - 1].getKind() == kind::EQUAL
          && res[n - 1][0].getKind() == kind::FUNCTION_TYPE
          && res[n - 1][1].getKind() == kind::FUNCTION_TYPE && equal
          && res[n - 1][0].getOperator() == res[n - 1][1].getOperator()){return CheckResult::True;}
      return CheckResult::False;
    }
    case VeritRule::EQ_CONGRUENT_PRED://No symm handling
    {  // TODO: What is the PREDICATE_TYPE
      bool equal;
      int n = res.end() - res.begin();
      for (auto i = 1; i < n - 1; i++)
      {
        if (!equalNodes(res[i][0][0], res[n - 1][0][0][i])
            || !equalNodes(res[i][0][1], res[n - 1][1][0][i])
            || res[i].getKind() != kind::NOT
            || res[i][0].getKind() != kind::EQUAL)
        {
          equal = false;
        }
      }
      if (res[0].toString() == cl.toString() && res[n - 1].getKind() == kind::EQUAL
          && res[n - 1][0].getKind() == kind::FUNCTION_TYPE
          && res[n - 1][1].getKind() == kind::FUNCTION_TYPE && equal
          && res[n - 1][0].getOperator() == res[n - 1][0].getOperator()){return CheckResult::True;}
      return CheckResult::False;
    }
    case VeritRule::DISTINCT_ELIM:{return CheckResult::NoCheck;}
    case VeritRule::LA_GENERIC:{return CheckResult::NoCheck;}
    case VeritRule::LIA_GENERIC:
    {
      return CheckResult::NoCheck;
    }
    case VeritRule::LA_DISEQUALITY:
    {  // Add that t1 t2 are numbers?
      if (res[0].toString() == cl.toString() && res[1].getKind() == kind::OR
          && res[1][0].getKind() == kind::EQUAL
          && res[1][1].getKind() == kind::NOT
          && res[1][1][0].getKind() == kind::LEQ
          && res[1][2].getKind() == kind::NOT
          && res[1][2][0].getKind() == kind::LEQ
          && equalNodes(res[1][0][0], res[1][1][0][0])
          && equalNodes(res[1][0][0], res[1][2][0][1])
          && equalNodes(res[1][0][1], res[1][1][0][1])
          && equalNodes(res[1][0][1], res[1][2][0][0]))
      {
        return CheckResult::True;
      }
      else
      {
        return CheckResult::False;
      }
    }
    /* Leave out rules 28-38 */
    case VeritRule::FORALL_INST:{//TODO: In the onomicon it seems as if there is an or instead of an cl
      bool success = true;
      //std::cout << res[1][0][0]<< std::endl;
      //std::cout << res[1][1] << std::endl;
      if  (res[0].toString() == cl.toString()
	  && res[1].getKind() == kind::OR
	  && res[1][0].getKind() == kind::NOT
	  && success){return CheckResult::NoCheck;}
      return CheckResult::False;
    }
    case VeritRule::EQ_RESOLUTION:
    {
    }  // same handling as resolution. TODO: delete
    case VeritRule::TH_RESOLUTION:
    {
    }
    case VeritRule::RESOLUTION:
    {  // This is not a real resolution check, but should be good enough. The
       // problem is that the order is unimportant here.
       // std::cout << std::endl;
      if (res[0].toString() != cl.toString())
      {
        return CheckResult::False;
      }
      std::vector<Node> clauses;

      for(int j = 1; j < (new_children[0].end()-new_children[0].begin());j++){
	 clauses.push_back(new_children[0][j]);
	 //std::cout << "added 1" << new_children[0][j] << std::endl;
      }
      for (int i = 1; i < (new_children.end() - new_children.begin());
           i++)
      {
        for(int j = 1; j < (new_children[i].end()-new_children[i].begin());j++){
	  bool new_clause = true;
          for(int k = 0; k < (clauses.end()-clauses.begin());k++){
	     //std::cout << "new_children[i][j] " << new_children[i][j] << std::endl;
	     //std::cout << "clauses[k].negate() " << clauses[k].notNode() << std::endl;
             if (equalNodes(new_children[i][j], clauses[k].notNode())
                 || equalNodes(new_children[i][j].notNode(), clauses[k]))
             {
               // std::cout << "deleted " << clauses[k] << std::endl;
               clauses.erase(clauses.begin() + k);
               new_clause = false;
               break;
             }
          }
          if(new_clause){
	    clauses.push_back(new_children[i][j]);
	    //std::cout << "added " << new_children[i][j] << std::endl;
	  }
	}
      }
      for(int i = 1; i < (res.end()-res.begin());i++){
        for(int k = 0; k < (clauses.end()-clauses.begin());k++){
          if (equalNodes(res[i], clauses[k]))
          {
            // std::cout << "deleted " << res[i]  << std::endl;
            clauses.erase(clauses.begin() + k);
            break;
          }
        }
      }
      // std::cout << "clauses "<< clauses << std::endl;
      if(clauses.empty()||(clauses.size()==1 && clauses[0]==nm->mkConst(false))){
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::REFL:
    {  // TODO
      //std::cout << (res[1][0] == res[1][1]) << std::endl;
      if (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString()
          && res[1].getKind() == kind::EQUAL
          && equalNodes(res[1][0], res[1][1]))
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::TRANS:  // Quick and ad-hoc fix not very clean or efficient
    {
      Node start;
      Node symm;
      if (new_children[0][0].toString() != cl.toString()
          || new_children[0][1].getKind() != kind::EQUAL
	  || new_children[1][0].toString() != cl.toString()
          || new_children[1][1].getKind() != kind::EQUAL)
      {
        return CheckResult::False;
      }

      bool success;
      bool success1 = true;
      bool success2 = true;
      bool success3 = true;
      bool success4 = true;
      if (equalNodes(new_children[0][1][0], new_children[1][1][0]))
      {
        start = new_children[0][1][1];
        symm = new_children[1][1][1];
        for (int i = 2; i < new_children.size();
             i++)  // TODO: does this need to be -1
        {
          if (new_children[i][0].toString() != cl.toString()
              || new_children[i][1].getKind() != kind::EQUAL)
          {
            success1 = false;
          }
          if (equalNodes(new_children[i][1][0], symm))
          {
            symm = new_children[i][1][1];
          }
          else if (equalNodes(new_children[i][1][1], symm))
          {
            symm = new_children[i][1][0];
          }
          else
          {
            success1 = false;
          }
        }
        if (res[0].toString() == cl.toString()
            && ((equalNodes(res[1][0], start)
                 && equalNodes(res[1][1], symm))
                || (equalNodes(res[1][0], symm)
                    && equalNodes(res[1][1], start)))
            && res[1].getKind() == kind::EQUAL)
        {
          success1 &= true;
        }
        success1 = false;
      }
      else if (equalNodes(new_children[0][1][0], new_children[1][1][1]))
      {
        start = new_children[0][1][1];
        symm = new_children[1][1][0];
        for (int i = 2; i < new_children.size();
             i++)  // TODO: does this need to be -1
        {
          if (new_children[i][0].toString() != cl.toString()
              || new_children[i][1].getKind() != kind::EQUAL)
          {
            success2 = false;
          }
          if (equalNodes(new_children[i][1][0], symm))
          {
            symm = new_children[i][1][1];
          }
          else if (equalNodes(new_children[i][1][1], symm))
          {
            symm = new_children[i][1][0];
          }
          else
          {
            success2 = false;
          }
        }
        if (res[0].toString() == cl.toString()
            && ((equalNodes(res[1][0], start)
                 && equalNodes(res[1][1], symm))
                || (equalNodes(res[1][0], symm)
                    && equalNodes(res[1][1], start)))
            && res[1].getKind() == kind::EQUAL)
        {
          success2 &= true;
        }
        success2 = false;
      }
      else if (equalNodes(new_children[0][1][1], new_children[1][1][0]))
      {
        start = new_children[0][1][0];
        symm = new_children[1][1][1];
        for (int i = 2; i < new_children.size();
             i++)  // TODO: does this need to be -1
        {
          if (new_children[i][0].toString() != cl.toString()
              || new_children[i][1].getKind() != kind::EQUAL)
          {
            success3 = false;
          }
          if (equalNodes(new_children[i][1][0], symm))
          {
            symm = new_children[i][1][1];
          }
          else if (equalNodes(new_children[i][1][1], symm))
          {
            symm = new_children[i][1][0];
          }
          else
          {
            success3 = false;
          }
        }
        if (res[0].toString() == cl.toString()
            && ((equalNodes(res[1][0], start)
                 && equalNodes(res[1][1], symm))
                || (equalNodes(res[1][0], symm)
                    && equalNodes(res[1][1], start)))
            && res[1].getKind() == kind::EQUAL)
        {
          success3 &= true;
        }
        success3 = false;
      }
      else if (equalNodes(new_children[0][1][1], new_children[1][1][1]))
      {
        start = new_children[0][1][0];
        symm = new_children[1][1][0];
        for (int i = 2; i < new_children.size();
             i++)  // TODO: does this need to be -1
        {
          if (new_children[i][0].toString() != cl.toString()
              || new_children[i][1].getKind() != kind::EQUAL)
          {
            success4 = false;
          }
          if (equalNodes(new_children[i][1][0], symm))
          {
            symm = new_children[i][1][1];
          }
          else if (equalNodes(new_children[i][1][1], symm))
          {
            symm = new_children[i][1][0];
          }
          else
          {
            success4 = false;
          }
        }
        if (res[0].toString() == cl.toString()
            && ((equalNodes(res[1][0], start)
                 && equalNodes(res[1][1], symm))
                || (equalNodes(res[1][0], symm)
                    && equalNodes(res[1][1], start)))
            && res[1].getKind() == kind::EQUAL)
        {
          success4 &= true;
        }
        success4 = false;
      }
      if (success1 || success2 || success3 || success4)
      {
        return CheckResult::True;
      }
      else
      {
        return CheckResult::False;
      }
      // std::cout << "start " <<  start << std::endl;
      // std::cout << "symm " << symm << std::endl;
     }
     case VeritRule::CONG:
     {
       for (int i = 0; i < new_children.size(); i++)
       {
         if (new_children[i][0].toString() != cl.toString()
             || new_children[i][1].getKind() != kind::EQUAL)
         {
           return CheckResult::False;
         }
         if (!(equalNodes(new_children[i][1][0], res[1][0][i])
               && equalNodes(new_children[i][1][1], res[1][1][i]))
             && !(equalNodes(new_children[i][1][0], res[1][1][i])
                  && equalNodes(new_children[i][1][1], res[1][0][i])))
         {
           return CheckResult::False;
         }
       }
       if (res.getKind() == kind::SEXPR && res[0].toString() == cl.toString()
           && res[1].getKind() == kind::EQUAL
           && res[1][0].getKind()
                  == res[1][1].getKind()  // TODO: check if function, seems to
                                          // be APPLY_UF at least sometimes
           && res[1][0].getOperator() == res[1][1].getOperator())
       {
         return CheckResult::True;
       }
       return CheckResult::False;
    }
    case VeritRule::AND:
    {
      bool equal = false;
      for (int i = 0;
           i < (new_children[0][1].end() - new_children[0][1].begin());
           i++)
      {
        if (equalNodes(new_children[0][1][i], res[1]))
        {
          equal = true;
        }
      }
      if (res[0].toString() == cl.toString()
          && new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::AND && equal)
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::TAUTOLOGIC_CLAUSE:
    {
      bool equal = false;
      for (int i = 0; i < (new_children[0].end() - new_children[0].begin());
           i++)
      {
        Node clause = new_children[0][i];
        for (int j = 0; j < (new_children[0].end() - new_children[0].begin());
             j++)
        {
          if (equalNodes(new_children[0][i], new_children[0][i].negate()))
          // check if .notNode() has to be used
          {
            equal = true;
          }
        }
      }
      if (res[0].toString() == cl.toString() && new_children[0][0] == cl
          && res[1] == nm->mkConst(true) && equal);
    }
    case VeritRule::NOT_OR: //DONE + TESTED
    {
      bool equal = false;
      for (int i = 0;
           i < (new_children[0][1][0].end() - new_children[0][1][0].begin());
           i++)
      {
	      //std::cout << "new_children[0][1][0][i] " << new_children[0][1][0][i] << std::endl;
	      //std::cout << "new_children[0][1][0][i].negate()  " << new_children[0][1][0][i].negate() << std::endl;
	      //std::cout << "new_children[0][1][0][i].notNode() " << new_children[0][1][0][i].notNode() <<std::endl;
              if (equalNodes(new_children[0][1][0][i].notNode(), res[1]))
              {
                equal = true;
              }
      }
      if (res[0].toString() == cl.toString() && new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::OR && equal){
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::OR: //DONE + TESTED
    {
      bool equal = true;
      if ((new_children[0][1].end() - new_children[0][1].begin())
          != (res.end() - res.begin() - 1))
      {
        return CheckResult::False;
      }
      for (int i = 0;
           i < (new_children[0][1].end() - new_children[0][1].begin());
           i++)
      {
        if (!equalNodes(new_children[0][1][i], res[i + 1]))
        {
          equal = false;
        }
      }
      if (res[0].toString() == cl.toString()
              && new_children[0][0].toString() == cl.toString()
              && new_children[0][1].getKind() == kind::OR && equal){
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_AND:{
      bool equal = true;
      if ((new_children[0][1][0].end() - new_children[0][1][0].begin())
          != (res.end() - res.begin() - 1))
      {
        return CheckResult::False;
      }

      for (int i = 0;
           i < (new_children[0][1][0].end() - new_children[0][1][0].begin());
           i++)
      {
        if ((!equalNodes(new_children[0][1][0][i].notNode(), res[i + 1]))
            || res[i + 1].getKind() != kind::NOT)
        {
          equal = false;
        }
      }
      if (res[0].toString() == cl.toString()
              && new_children[0][0].toString() == cl.toString()
              && new_children[0][1].getKind() == kind::NOT
	      && new_children[0][1][0].getKind() == kind::AND
	      && equal){
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::IMPLIES://tested
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::IMPLIES
          && equalNodes(new_children[0][1][0], res[1][0])
          && res[1].getKind() == kind::NOT
          && equalNodes(new_children[0][1][1], res[2])
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_IMPLIES1:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::IMPLIES
          && equalNodes(new_children[0][1][0][0], res[1])
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_IMPLIES2:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::IMPLIES
          && equalNodes(new_children[0][1][0][1], res[1][0])
          && res[1].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQUIV1:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::EQUAL
          && equalNodes(new_children[0][1][0], res[1][0])
          && equalNodes(new_children[0][1][1], res[2])
          && res[1].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::EQUIV2:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::EQUAL
          && equalNodes(new_children[0][1][0], res[1])
          && equalNodes(new_children[0][1][1], res[2][0])
          && res[2].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_EQUIV1:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::EQUAL
          && equalNodes(new_children[0][1][0][0], res[1])
          && equalNodes(new_children[0][1][0][1], res[2])
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_EQUIV2:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::EQUAL
          && equalNodes(new_children[0][1][0][0], res[1][0])
          && equalNodes(new_children[0][1][0][1], res[2][0])
          && res[1].getKind() == kind::NOT && res[2].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::ITE1:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::ITE
          && equalNodes(new_children[0][1][0], res[1])
          && equalNodes(new_children[0][1][2], res[2])
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::ITE2:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::ITE
          && equalNodes(new_children[0][1][0], res[1][0])
          && equalNodes(new_children[0][1][1], res[2])
          && res[1].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_ITE1:
    {
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::ITE
          && equalNodes(new_children[0][1][0][0], res[1])
          && equalNodes(new_children[0][1][0][2], res[2][0])
          && res[2].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::NOT_ITE2:
    {  // TODO: For all rules this should not be ifs but try catches, since
       // maybe children does not has [0][1][0][0] element
      if (new_children[0][0].toString() == cl.toString()
          && new_children[0][1].getKind() == kind::NOT
          && new_children[0][1][0].getKind() == kind::ITE
          && equalNodes(new_children[0][1][0][0], res[1][0])
          && equalNodes(new_children[0][1][0][1], res[2][0])
          && res[2].getKind() == kind::NOT && res[1].getKind() == kind::NOT
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::DUPLICATED_LITERALS:
    {
      std::vector<Node> resVec;
      resVec.insert(resVec.begin(),res.begin()+1,res.end()); //TODO: DO THIS EVERYWHERE INSTEAD OF FOR LOOP

      std::vector<Node> childVec;
      childVec.insert(childVec.begin(),new_children[0].begin()+1, new_children[0].end());

      Node lastElement = res[0];
      Node nextElement = res[1];
      bool alreadyEncountered;
      std::vector<Node> childVec2;
      int j = 0;

      for (int i = 0; i < childVec.size(); i++)
      {
        if (!equalNodes(childVec[i], lastElement))
        {
          if (!equalNodes(childVec[i], nextElement))
          {
            if (std::find(childVec2.begin(), childVec.end(), childVec[i])
                == childVec2.end())
            {
              return CheckResult::False;
            }
          }
          lastElement = resVec[j];
          if (j != resVec.size() - 1)
          {
            nextElement = resVec[j + 1];
          }
          j++;
          childVec2.push_back(childVec[i]);
        }
      }

      if (new_children[0][0].toString() == cl.toString()
          && res[0].toString() == cl.toString())
      {
        return CheckResult::True;
      }
      return CheckResult::False;
    }
    case VeritRule::ITE_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::EQ_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::AND_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::OR_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::NOT_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::IMPLIES_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::EQUIV_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::BOOL_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::QUANTIFIER_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::DIV_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::PROD_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::UNARY_MINUS_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::MINUS_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::SUM_SIMPLIFY:{return CheckResult::NoCheck;}
    case VeritRule::COMP_SIMPLIFY:{return CheckResult::NoCheck;}
    default:
    {
      return CheckResult::NotTranslated;
    }
  }
}
//Add res.getKind() == kind::SEXPR everywhere
static bool veritProofCheckerInternal(std::shared_ptr<ProofNode> pfn)
{
   //std::cout << " CHECK CHILD ";
   //std::cout  << pfn->getResult() << " ";
   //std::cout<<veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())))
   //<< std::endl;
  bool success = true;

  VeritRule id = static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()));
  Node res = pfn->getArguments()[2];  //Give this as arguments to veritProofChecker
  std::vector<Node> new_children;
  for (std::shared_ptr<ProofNode> child : pfn->getChildren())
  {
    new_children.push_back(child->getArguments()[2]);
  }

  try
  {
    CheckResult check = checkStep(pfn);

    if (check == CheckResult::True)
    {  // TODO: indent
      Trace("verit-checker")
          << "... check succeeded " << res << " " << veritRuletoString(id)
          << " " << new_children << std::endl;
    }
    else if (check == CheckResult::NotTranslated)
    {
      Trace("verit-checker")
          << "... check not translated yet " << res << " "
          << veritRuletoString(id) << " " << new_children << std::endl;

      Trace("verit-checker-debug")
          << "... check not translated yet " << res << " "
          << veritRuletoString(id) << " " << new_children << std::endl;

      Trace("verit-checker-failed")
          << "... check not translated yet " << res << " "
          << veritRuletoString(id) << " " << new_children << std::endl;
      success = false;
    }
    else if (check == CheckResult::False)
    {
      Trace("verit-checker")
          << "... check failed " << res << " " << veritRuletoString(id) << " "
          << new_children << std::endl;

      Trace("verit-checker-debug")
          << "... check failed " << res << " " << veritRuletoString(id) << " "
          << new_children << std::endl;

      Trace("verit-checker-failed")
          << "... check failed " << res << " " << veritRuletoString(id) << " "
          << new_children << std::endl;
      success = false;
    }
    else
    {
      Trace("verit-checker")
          << "... check manually " << res << " " << veritRuletoString(id) << " "
          << new_children << std::endl;

      Trace("verit-checker-debug")
          << "... check manually " << res << " " << veritRuletoString(id) << " "
          << new_children << std::endl;
    }
  }
  catch (...)
  {  // TODO: This is not working
    std::cout << "in exception" << std::endl;
    Trace("verit-checker-debug")
        << "... check manually " << res << " " << veritRuletoString(id) << " "
        << new_children << std::endl;
    Trace("verit-checker-failed")
        << "... check failed " << res << " " << veritRuletoString(id) << " "
        << new_children << std::endl;
  }
  for (auto child : pfn->getChildren())
  {
    success &= veritProofCheckerInternal(child);
  }
  return success;
}

static void veritProofChecker(std::shared_ptr<ProofNode> pfn, std::ostream& out)
{
  NodeManager* nm = NodeManager::currentNM();
  bool success = veritProofCheckerInternal(pfn);
  Node cl = nm->mkBoundVar("cl", nm->stringType());
  Node res = pfn->getArguments()[2];  // TODO: catch if this is not possible,
                                      // also in checkStep
  if (res.toString() != nm->mkNode(kind::SEXPR, cl).toString())
  {
    success = false;
    Trace("verit-checker-debug") << "... last step is not (cl). " << std::endl;
    Trace("verit-checker-failed") << "... last step is not (cl). " << std::endl;
  }
  if (success)
  {
    out << "Proof check succeeded."
        << "\n";
  }
  else
  {
    out << "Proof check failed."
        << "\n";
  }
  out << "\n";
  out << "\n";
}
}  // namespace proof

}  // namespace CVC4

#endif
