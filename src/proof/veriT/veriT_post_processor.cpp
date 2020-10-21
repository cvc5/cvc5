/*********************                                                        */
/*! \file veriT_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into veriT proof nodes
 **/

#include "proof/veriT/veriT_post_processor.h"
#include "proof/veriT/veriT_printer.h" 
#include <cstdlib>
#include <functional>
#include <memory>
#include <vector>

namespace CVC4 {

namespace proof {

VeriTProofPostprocessCallback::VeriTProofPostprocessCallback(ProofNodeManager* pnm){
  d_pnm = pnm;
}

void VeriTProofPostprocessCallback::initializeUpdate(){}

bool VeriTProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
		bool& continueUpdate){
  //In case of a 1-1 correspondence of the CVC4 proof rule and the veriT proof rule the proof node is not updated.
	//The general template for this is:
	//
  // ======== Proof Rule 
  // Children: (P1 ... Pn)
  // Arguments: (A1 ... An)
  // ---------------------
  // Conclusion: (C)
	//
	// proof rule: VeriT proof rule
	// proof term: (C)
	// premises: (P1 ... Pn)
	// args: (A1 ... An) TODO: remove args?
	//
	// I.e. only the proof rule changes. The veriTPrinter will map any remaining CVC4 rule to the corresponding VeriT rule during printing.

	// TEMP: For now translate all!
	
	switch(pn->getRule()){
    case PfRule::VERIT_RULE: return false;
  }
	return true;
} 

static void printCurrentNode(Node res,
				           PfRule id,
				           const std::vector<Node>& children,
				           const std::vector<Node>& args){

	//Temp code for printing the current proof node 
	std::cout << "Print current node information" <<std::endl;
	std::cout << "  (" << id << ",{";
  
	if(children.size() > 0)
		std::cout << children[0];

for(int i=1;i<children.size();i++){
	std::cout << "," << children[i];
}
std::cout << "},{";

if(args.size() > 0)
	std::cout << args[0];

for(int i=1;i<args.size();i++){
	std::cout << "," << args[i];
}

std::cout<<"})"<<std::endl;

}

bool VeriTProofPostprocessCallback::update(Node res,
								 PfRule id,
								 const std::vector<Node>& children,
								 const std::vector<Node>& args,
								 CDProof* cdp,
								 bool& continueUpdate){

printCurrentNode(res,id,children,args);
NodeManager* nm = NodeManager::currentNM();

std::vector<Node> new_args = std::vector<Node>();	

std::cout << res.toExpr() << std::endl;	

//TODO: or and cl have to be exchanged while printing?



switch(id){  
	//================================================= Core rules
  //======================== Assume and Scope
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion: F
	//
	// proof rule: assume
	// proof term: (F)
	// premises: ()
	// args: ()
	case PfRule::ASSUME:{		//TODO: ASSUMPTIONS SHOULD NOT BE PRINTED SEVERAL TIMES				
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::ASSUME)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;

	}
  // ======== Scope (a binder for assumptions)
  // Children: (P:F)
  // Arguments: (F1, ..., Fn)
  // --------------
  // Conclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false
	//
	// proof rule: anchor
	// proof term: 
	// premises: 
	// args: (F1, ..., Fn)
	case PfRule::SCOPE:{
			//TODO: Ask Haniel about anchor in veriT
	}
  //================================================= Boolean rules
  // ======== Resolution
  // Children:
  //  (P1:(or F_1 ... F_i-1 F_i F_i+1 ... F_n),
  //   P2:(or G_1 ... G_j-1 G_j G_j+1 ... G_m))
  //
  // Arguments: (F_i)
  // ---------------------
  // Conclusion: (or F_1 ... F_i-1 F_i+1 ... F_n G_1 ... G_j-1 G_j+1 ... G_m)
  // where
  //   G_j = (not F_i)
	//
	// proof rule: resolution
	// proof term: (or F_1 ... F_i-1 F_i+1 ... F_n G_1 ... G_j-1 G_j+1 ... G_m)
	// premises: (P1:(or F_1 ... F_i-1 F_i F_i+1 ... F_n),
  //            P2:(or G_1 ... G_j-1 G_j G_j+1 ... G_m))
	// args: ()
	case PfRule::RESOLUTION:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Chain Resolution
  // Children: (P1:(or F_{1,1} ... F_{1,n1}), ..., Pm:(or F_{m,1} ... F_{m,nm}))
  // Arguments: (L_1, ..., L_{m-1})
  // ---------------------
  // Conclusion: C_m'
  // where
  //   let "C_1 <>_l C_2" represent the resolution of C_1 with C_2 with pivot l,
  //   let C_1' = C_1 (from P_1),
  //   for each i > 1, C_i' = C_i <>_L_i C_{i-1}'	
	//
	// proof rule: resolution
	// proof term: (C_m')
	// premises: (P1:(or F_{1,1} ... F_{1,n1}), ..., Pm:(or F_{m,1} ... F_{m,nm}))
	// args: ()
	case PfRule::CHAIN_RESOLUTION:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Factoring
  // Children: (P:C1)
  // Arguments: ()
  // ---------------------
  // Conclusion: C2
  // where
  //  Set representations of C1 and C2 is the same and the number of literals in
  //  C2 is smaller than that of C1
	//
	//  proof rule: duplicate_literals
	//  proof term: (C_m')
	//  premises: (P:C1)
	//  args: ()
	case PfRule::FACTORING:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::DUPLICATE_LITERALS)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}  
  // ======== Reordering
  // Children: (P:C1)
  // Arguments: (C2)
  // ---------------------
  // Conclusion: C2
  // where
  //  Set representations of C1 and C2 is the same but the number of literals in
  //  C2 is the same of that of C1
	//
	// proof rule: 
	// proof term:
	// premises:
	// args: 
	case PfRule::REORDERING:{
		//TODO
	}  
  // ======== Split
  // Children: none
  // Arguments: (F)
  // ---------------------
  // Conclusion: (or F (not F))
	//
	// proof rule: not_not
	// proof term: (VP1:(or (not (not (not F))) F))
	// premises: 
	// args: ()
	//
	// proof rule: not_not
	// proof term: (VP2:(or (not (not (not (not F)))) (not F))
	// premises: VP1
	// args: ()
	//
	// proof rule: resolution
	// proof term: (or F (not F))
	// premises: VP2
	// args: ()
	case PfRule::SPLIT:{
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_NOT)));
		Node three_neg = nm->mkNode(kind::OR,(nm->mkNode(kind::NOT,nm->mkNode(kind::NOT,nm->mkNode(kind::NOT,args[0]))),args[0])); 
		new_args.push_back(three_neg);
		std::cout << three_neg.toExpr() << std::endl;
		cdp->addStep(three_neg,PfRule::VERIT_RULE,children,new_args);

		new_args.clear();
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_NOT)));
		Node four_neg = nm->mkNode(kind::OR,(nm->mkNode(nm->mkNode(kind::NOT,nm->mkNode(kind::NOT,nm->mkNode(kind::NOT,args[0]))),nm->mkNode(kind::NOT,args[0])))); 
		new_args.push_back(four_neg);
		cdp->addStep(four_neg,PfRule::VERIT_RULE,{three_neg},new_args);

		new_args.clear();
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,{four_neg,three_neg},new_args);

		return true;							 
	}
  // ======== Equality resolution
  // Children: (P1:F1, P2:(= F1 F2))
  // Arguments: none
  // ---------------------
  // Conclusion: (F2)
  // 
	case PfRule::EQ_RESOLVE:{
		//TODO Equiv elim + resolution		
		//Find out more about difference terms and formulae in cvc4	
	}
  // ======== Modus ponens
  // Children: (P1:F1, P2:(=> F1 F2))
  // Arguments: none
  // ---------------------
  // Conclusion: (F2)
  //
	// proof rule: implies
	// proof term: (VP:(or (not F1) F2))
	// premises: (P2:(=> F1 F2))
	// args: ()
	//
	// proof rule: resolution
	// proof term: (F2)
	// premises: (P1:F1) (VP:(or (not F1) F2))
	// args: ()
	case PfRule::MODUS_PONENS:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::IMPLIES)));
		Node n = nm->mkNode(kind::OR,nm->mkNode(kind::NOT,children[0]),res);	
		new_args.push_back(n);
		cdp->addStep(n,PfRule::VERIT_RULE,{children[1]},new_args);

		new_args.clear();
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,{n,children[0]},new_args);

		return true;											
	}
	// ======== Double negation elimination
  // Children: (P:(not (not F)))
  // Arguments: none
  // ---------------------
  // Conclusion: (F)
	//
	// proof rule: not_not
	// proof term: (VP:(or (not (not (not F))) F))
	// premises: 
	// args: ()
	//
	// proof rule: resolution
	// proof term: (F)
	// premises: (VP:(or (not (not (not F))) F)) (P:(not (not F)))
	// args: ()
	case PfRule::NOT_NOT_ELIM:{
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_NOT)));
		Node n = nm->mkNode(kind::OR,nm->mkNode(kind::NOT,children[0]),res);
		new_args.push_back(n); 	
		cdp->addStep(n,PfRule::VERIT_RULE,{},new_args);

		new_args.clear();
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,{children[0],n},new_args);

		return true;
	}  
	// ======== Contradiction
  // Children: (P1:F P2:(not F))
  // Arguments: ()
  // ---------------------
  // Conclusion: false
	//
	// proof rule: resolution
	// proof term: ()
	// premises: (P1:F) (P2:(not F))
	// args: ()
	case PfRule::CONTRA:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(Node::null()); //print this as empty	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== And elimination
  // Children: (P:(and F1 ... Fn))
  // Arguments: (i)
  // ---------------------
  // Conclusion: (Fi)
	//
	// proof rule: and
	// proof term: (Fi)
	// premises: (P:(and F1 ... Fn))
	// args: ()
	case PfRule::AND_ELIM:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::AND)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	// ======== And introduction
  // Children: (P1:F1 ... Pn:Fn))
  // Arguments: ()
  // ---------------------
  // Conclusion: (and P1 ... Pn)
	//
	// First the tautology (or (and F1 ... Fn) (not F1) ... (not Fn))) is introduced. Then, the resolution rule is applied n times where Vpi+1 is obtained by applying resolution to VPi:(or (and F1 ... Fn) (not Fi) ... (not Fn))) and Fi.
	//
	// proof rule: and_neg
	// proof term: (VP1:(or (and F1 ... Fn) (not F1) ... (not Fn)))
	// premises: ()
	// args: ()
	//
	// proof rule: resolution
	// proof term: (VP2:(or (and F1 ... Fn) (not F2) ... (not Fn)))
	// premises: (VP1:(or (and F1 ... Fn) (not F1) ... (not Fn))) P1
	// args: ()
	//
	// ...
	//
	// proof rule: resolution
	// proof term: (VP:(or (and F1 ... Fn))
	// premises: (VPn:(or (and F1 ... Fn) (not Fn))) Fn
	// args: () 


	case PfRule::AND_INTRO:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::AND_NEG)));

		std::vector<Node> neg_Nodes;
		neg_Nodes.push_back(nm->mkNode(kind::AND,children));
	 	for(int i = 0; i < children.size(); i++){
	    neg_Nodes.push_back(nm->mkNode(kind::NOT,children[i]));
	  }

		Node and_neg_Node = nm->mkNode(kind::OR,neg_Nodes);	
		new_args.push_back(and_neg_Node); 
		cdp->addStep(and_neg_Node,PfRule::VERIT_RULE,{},new_args);

		for(int i = 0; i < children.size(); i++){
			new_args.clear();
		  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
			neg_Nodes.erase(neg_Nodes.begin()+1);
			Node new_and_neg_Node; 
			if(i<children.size()-1){
				new_and_neg_Node = nm->mkNode(kind::OR,neg_Nodes);	
			}
			else{
				new_and_neg_Node = neg_Nodes[0];
			}
     	new_args.push_back(new_and_neg_Node);
			cdp->addStep(new_and_neg_Node,PfRule::VERIT_RULE,{children[i],and_neg_Node},new_args);
			and_neg_Node = new_and_neg_Node;
		}


		return true;
	}
	// ======== Not Or elimination
	// Children: (P:(not (or F1 ... Fn)))
	// Arguments: (i)
	// ---------------------
	// Conclusion: (not Fi)
	//
	// proof rule: not_or
	// proof term: (not Fi)
	// premises: (P:(not (or F1 ... Fn)))
	// args: ()
	case PfRule::NOT_OR_ELIM:{			
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_OR)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
  }	
	// ======== Implication elimination
  // Children: (P:(=> F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) F2)
	//
	// proof rule: implies
	// proof term: (or (not F1) F2)
	// premises: (P:(=> F1 F2))
	// args: ()
	case PfRule::IMPLIES_ELIM:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::IMPLIES)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	// ======== Not Implication elimination version 1
  // Children: (P:(not (=> F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (F1)
	//
	// proof rule: not_implies1
	// proof term: (F1)
	// premises: (P:(not (=> F1 F2)))
	// args: ()
	case PfRule::NOT_IMPLIES_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_IMPLIES1)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Not Implication elimination version 2
  // Children: (P:(not (=> F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (not F2)
	//
	// proof rule: not_implies2
	// proof term: (not F2)
	// premises: (P:(not (=> F1 F2)))
	// args: ()
	case PfRule::NOT_IMPLIES_ELIM2:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_IMPLIES2)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Equivalence elimination version 1
  // Children: (P:(= F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) F2)
	//
	// proof rule: equiv1
	// proof term: (or (not F1) F2)
	// premises: (P:(= F1 F2))
	// args: ()
	case PfRule::EQUIV_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::EQUIV1)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	// ======== Equivalence elimination version 2
  // Children: (P:(= F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 (not F2))
	//
	// proof rule: equiv2
	// proof term: (or F1 (not F2))
	// premises: (P:(= F1 F2))
	// args: ()
	case PfRule::EQUIV_ELIM2:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::EQUIV2)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Not Equivalence elimination version 1
  // Children: (P:(not (= F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 F2)
	// 
	// proof rule: not_equiv1
	// proof term: (or F1 F2)
	// premises: (P:(not (= F1 F2)))
	// args: ()
	case PfRule::NOT_EQUIV_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_EQUIV1)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Not Equivalence elimination version 2
  // Children: (P:(not (= F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) (not F2))
	// 
	// proof rule: not_equiv1
	// proof term: (or (not F1) (not F2))
	// premises: (P:(not (= F1 F2)))
	// args: ()
	case PfRule::NOT_EQUIV_ELIM2:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_EQUIV2)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== XOR elimination version 1
  // Children: (P:(xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 F2)
  //
	// proof rule: XOR1
	// proof term: (or F1 F2)
	// premises: (P:(xor F1 F2))
	// args: ()
	case PfRule::XOR_ELIM1:{
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::XOR1)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	// ======== XOR elimination version 2
  // Children: (P:(not (xor F1 F2))))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 (not F2))
	//
	// proof rule: XOR2
	// proof term: (or F1 (not F2))
	// premises: (P:(not (xor F1 F2)))
	// args: ()
	case PfRule::XOR_ELIM2:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::XOR2)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}  
  // ======== Not XOR elimination version 1
  // Children: (P:(not (xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 (not F2))
	//
	// proof rule: NOT_XOR1
	// proof term: (or F1 (not F2))
	// premises: (P:(not (xor F1 F2)))
	// args: ()
	case PfRule::NOT_XOR_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_XOR1)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== Not XOR elimination version 2
  // Children: (P:(not (xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) F2)
	//
	// proof rule: NOT_XOR1
	// proof term: (or (not F1) F2)
	// premises: (P:(not (xor F1 F2)))
	// args: ()
	case PfRule::NOT_XOR_ELIM2:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_XOR2)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	// ======== ITE elimination version 1
  // Children: (P:(ite C F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not C) F1)
	// 
	// proof rule: ite2
	// proof term: (or (not C) F1)
	// premises: (P:(ite C F1 F2))
	// args: ()
	case PfRule::ITE_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::ITE2)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
  // ======== ITE elimination version 2
  // Children: (P:(ite C F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or C F2)
	//  
	// proof rule: ite1
	// proof term: (or C F2)
	// premises: (P:(ite C F1 F2))
	// args: ()
	case PfRule::ITE_ELIM2:{
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::ITE1)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
  }
  // ======== Not ITE elimination version 1
  // Children: (P:(not (ite C F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not C) (not F1))
	//  
	// proof rule: not_ite2
	// proof term: (or (not C) (not F1))
	// premises: (P:(not (ite C F1 F2)))
	// args: ()
	case PfRule::NOT_ITE_ELIM1:{
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_ITE2)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;										 
	}
  // ======== Not ITE elimination version 1
  // Children: (P:(not (ite C F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or C (not F2))
	// 
	// proof rule: not_ite1
	// proof term: (or C (not F2))
	// premises: (P:(not (ite C F1 F2)))
	// args: ()
	case PfRule::NOT_ITE_ELIM2:{
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_ITE1)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;										 
	}



	case PfRule::CONG:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::CONG)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}

	default:
		if(new_args.empty()){
			new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::UNDEFINED)));
		}
		new_args.push_back(res);	
		new_args.insert(new_args.end(),args.begin(),args.end());
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
  }
	return true;
}

VeriTProofPostprocess::VeriTProofPostprocess(ProofNodeManager* pnm,ProofNodeUpdaterCallback &cb):ProofNodeUpdater{pnm,cb}{}

VeriTProofPostprocess::~VeriTProofPostprocess(){}

void VeriTProofPostprocess::process(std::shared_ptr<ProofNode> pf){
	ProofNodeUpdater::process(pf);
}


	
	
}

}
