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
#include <cstdlib>
#include <functional>
#include <memory>
#include <vector>

namespace CVC4 {

namespace proof {

VeriTProofPostprocessCallback::VeriTProofPostprocessCallback(ProofNodeManager* pnm):d_pnm(pnm){
  d_nm = NodeManager::currentNM();
}

void VeriTProofPostprocessCallback::initializeUpdate(){
  //d_nm = NodeManager::currentNM();
}

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

//Temp code for printing the current proof node 
static void printCurrentNode(Node res,
				           PfRule id,
				           const std::vector<Node>& children,
				           const std::vector<Node>& args){

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

bool VeriTProofPostprocessCallback::addVeriTStep(Node res,
								 												 				 VeriTRule rule,
																				 				 const std::vector<Node>& children,
								 												 				 const std::vector<Node>& args,
								 												 				 CDProof& cdp){
    std::vector<Node> new_args = std::vector<Node>();	
		new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(rule)));
		new_args.push_back(res);
		new_args.insert(new_args.end(),args.begin(),args.end());
		cdp.addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
}

bool VeriTProofPostprocessCallback::update(Node res,
								 PfRule id,
								 const std::vector<Node>& children,
								 const std::vector<Node>& args,
								 CDProof* cdp,
								 bool& continueUpdate){

std::vector<Node> new_args = std::vector<Node>();	

//Test print

printCurrentNode(res,id,children,args);

std::cout << res.toExpr() << std::endl;	


//TODO: or and cl have to be exchanged while printing?
//TODO: the result of resolution could be an empty clause (i.e. not false but Node::null)

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
	case PfRule::ASSUME:{				
		return addVeriTStep(res,VeriTRule::ASSUME,children,{},*cdp);
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
	/*case PfRule::SCOPE:{
			//TODO: Ask Haniel about anchor in veriT

	  for(int i = 0; i < args.size(); i++){
		  addVeriTStep(args[i],VeriTRule::ASSUME,{},{},*cdp);	
		}

		addVeriTStep(res,VeriTRule::ANCHOR,children,args,*cdp);

		//TODO: Adding the last step (introducing the implication) is not feasible. It is better to print it when the scope statement comes up
		//Add this to the final version of printer. 		
		return true;
	}*/
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
		return addVeriTStep(res,VeriTRule::RESOLUTION,children,{},*cdp);
		//TODO: Is a reordering step needed? It is not clear from the onomicon how this works in veriT
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
		return addVeriTStep(res,VeriTRule::RESOLUTION,children,{},*cdp);
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
	//  proof term: (C2)
	//  premises: (P:C1)
	//  args: ()
	case PfRule::FACTORING:{
		return addVeriTStep(res,VeriTRule::DUPLICATE_LITERALS,children,{},*cdp);
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
	// premises: () 
	// args: ()
	//
	// proof rule: not_not
	// proof term: (VP2:(or (not (not (not (not F)))) (not F))
	// premises: ()
	// args: ()
	//
	// proof rule: resolution
	// proof term: (or F (not F))
	// premises: VP1 VP2
	// args: ()
	case PfRule::SPLIT:{
		Node vp1 = d_nm->mkNode(kind::OR,(d_nm->mkNode(kind::NOT,d_nm->mkNode(kind::NOT,d_nm->mkNode(kind::NOT,args[0]))),args[0]));
	  addVeriTStep(vp1,VeriTRule::NOT_NOT,{},{},*cdp);	

		Node vp2 = d_nm->mkNode(kind::OR,(d_nm->mkNode(d_nm->mkNode(kind::NOT,d_nm->mkNode(kind::NOT,d_nm->mkNode(kind::NOT,args[0]))),d_nm->mkNode(kind::NOT,args[0])))); 
		addVeriTStep(vp2,VeriTRule::NOT_NOT,{},{},*cdp);

		addVeriTStep(res,VeriTRule::RESOLUTION,{vp1,vp2},{},*cdp);

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
		Node vp = d_nm->mkNode(kind::OR,d_nm->mkNode(kind::NOT,children[0]),res);
	  addVeriTStep(vp,VeriTRule::IMPLIES,{children[1]},{},*cdp);	
		addVeriTStep(res,VeriTRule::RESOLUTION,{vp,children[0]},{},*cdp);
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
		Node vp = d_nm->mkNode(kind::OR,d_nm->mkNode(kind::NOT,children[0]),res);
		addVeriTStep(vp,VeriTRule::NOT_NOT,{},{},*cdp);
		addVeriTStep(res,VeriTRule::RESOLUTION,{children[0],vp},{},*cdp);
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
	  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
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
		return addVeriTStep(res,VeriTRule::AND,children,{},*cdp);
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

		std::vector<Node> neg_Nodes;
		neg_Nodes.push_back(d_nm->mkNode(kind::AND,children));
	 	for(int i = 0; i < children.size(); i++){
	    neg_Nodes.push_back(d_nm->mkNode(kind::NOT,children[i]));
	  }

		Node and_neg_Node = d_nm->mkNode(kind::OR,neg_Nodes);	
		addVeriTStep(and_neg_Node,VeriTRule::AND_NEG,{},{},*cdp);

		for(int i = 0; i < children.size(); i++){
			neg_Nodes.erase(neg_Nodes.begin()+1);
			Node new_and_neg_Node; 
			if(i<children.size()-1){
				new_and_neg_Node = d_nm->mkNode(kind::OR,neg_Nodes);	
			}
			else{
				new_and_neg_Node = neg_Nodes[0];
			}
			addVeriTStep(new_and_neg_Node,VeriTRule::RESOLUTION,{children[i],and_neg_Node},{},*cdp);
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
		return addVeriTStep(res,VeriTRule::NOT_OR,children,{},*cdp);										 
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
		return addVeriTStep(res,VeriTRule::IMPLIES,children,{},*cdp);									
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
		return addVeriTStep(res,VeriTRule::NOT_IMPLIES1,children,{},*cdp);									
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
		return addVeriTStep(res,VeriTRule::NOT_IMPLIES2,children,{},*cdp);									
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
		return addVeriTStep(res,VeriTRule::EQUIV1,children,{},*cdp);	
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
		return addVeriTStep(res,VeriTRule::EQUIV2,children,{},*cdp);	
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
		return addVeriTStep(res,VeriTRule::NOT_EQUIV1,children,{},*cdp);	
	}
  // ======== Not Equivalence elimination version 2
  // Children: (P:(not (= F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) (not F2))
	// 
	// proof rule: not_equiv2
	// proof term: (or (not F1) (not F2))
	// premises: (P:(not (= F1 F2)))
	// args: ()
	case PfRule::NOT_EQUIV_ELIM2:{
		return addVeriTStep(res,VeriTRule::NOT_EQUIV2,children,{},*cdp);	
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
		return addVeriTStep(res,VeriTRule::XOR1,children,{},*cdp);	
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
		return addVeriTStep(res,VeriTRule::XOR2,children,{},*cdp);	
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
		return addVeriTStep(res,VeriTRule::NOT_XOR1,children,{},*cdp);
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
		return addVeriTStep(res,VeriTRule::NOT_XOR2,children,{},*cdp);
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
		return addVeriTStep(res,VeriTRule::ITE2,children,{},*cdp);
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
		return addVeriTStep(res,VeriTRule::ITE1,children,{},*cdp);
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
		return addVeriTStep(res,VeriTRule::NOT_ITE2,children,{},*cdp);
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
		return addVeriTStep(res,VeriTRule::NOT_ITE1,children,{},*cdp);
	}

  //================================================= De Morgan rules
  // ======== Not And
  // Children: (P:(not (and F1 ... Fn))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) ... (not Fn))
	//
	// proof rule: not_and
	// proof term: (or (not F1) ... (not Fn))
	// premises: (P:(not (and F1 ... Fn))
	// args: ()
	case PfRule::NOT_AND:{
		return addVeriTStep(res,VeriTRule::NOT_AND,children,{},*cdp);
	}
  
	//================================================= CNF rules
  // ======== CNF And Pos
  // Children: ()
  // Arguments: ((and F1 ... Fn), i)
  // ---------------------
  // Conclusion: (or (not (and F1 ... Fn)) Fi)
	//
	// proof rule: and_pos
	// proof term: (or (not (and F1 ... Fn)) Fi)
	// premises: ()
	// args: ()
  case PfRule::CNF_AND_POS:{
		return addVeriTStep(res,VeriTRule::AND_POS,children,{},*cdp);
	}
	// ======== CNF And Neg
  // Children: ()
  // Arguments: ((and F1 ... Fn))
  // ---------------------
  // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
	//
	// proof rule: and_neg
	// proof term: (or (and F1 ... Fn) (not F1) ... (not Fn))
	// premises: ()
	// args: ()
  case PfRule::CNF_AND_NEG:{
		return addVeriTStep(res,VeriTRule::AND_NEG,children,{},*cdp);
	}
  // ======== CNF Or Pos
  // Children: ()
  // Arguments: ((or F1 ... Fn))
  // ---------------------
  // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)	
	// 
	// proof rule: or_pos
	// proof term: (or (not (or F1 ... Fn)) F1 ... Fn)	
	// premises: ()
	// args: ()
  case PfRule::CNF_OR_POS:{
		return addVeriTStep(res,VeriTRule::OR_POS,children,{},*cdp);
	}
  // ======== CNF Or Neg
  // Children: ()
  // Arguments: ((or F1 ... Fn), i)
  // ---------------------
  // Conclusion: (or (or F1 ... Fn) (not Fi))	
	// 
	// proof rule: or_neg 
	// proof term: (or (or F1 ... Fn) (not Fi))	
	// premises: ()
	// args: ()
	case PfRule::CNF_OR_NEG:{
		return addVeriTStep(res,VeriTRule::OR_NEG,children,{},*cdp);
	}
  // ======== CNF Implies Pos
  // Children: ()
  // Arguments: ((implies F1 F2))
  // ---------------------
  // Conclusion: (or (not (implies F1 F2)) (not F1) F2)	
	// 
	// proof rule: implies_pos 
	// proof term: (or (not (implies F1 F2)) (not F1) F2)	
	// premises: ()
	// args: ()
	case PfRule::CNF_IMPLIES_POS:{
		return addVeriTStep(res,VeriTRule::IMPLIES_POS,children,{},*cdp);
	}
  // ======== CNF Implies Neg version 1
  // Children: ()
  // Arguments: ((implies F1 F2))
  // ---------------------
  // Conclusion: (or (implies F1 F2) F1)	
	// 
	// proof rule: implies_neg1 
	// proof term: (or (implies F1 F2) F1)	
	// premises: ()
	// args: ()
	case PfRule::CNF_IMPLIES_NEG1:{
		return addVeriTStep(res,VeriTRule::IMPLIES_NEG1,children,{},*cdp);
	}  
	// ======== CNF Implies Neg version 2
  // Children: ()
  // Arguments: ((implies F1 F2))
  // ---------------------
  // Conclusion: (or (implies F1 F2) (not F2))	
	// 
	// proof rule: implies_neg2 
	// proof term: (or (implies F1 F2) (not F2))
	// premises: ()
	// args: ()
	case PfRule::CNF_IMPLIES_NEG2:{
		return addVeriTStep(res,VeriTRule::IMPLIES_NEG2,children,{},*cdp);
	}
  // ======== CNF Equiv Pos version 1
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (not (= F1 F2)) (not F1) F2)	
	// 
	// proof rule: equiv_pos2 
	// proof term: (or (not (= F1 F2)) (not F1) F2)	
	// premises: ()
	// args: ()
	case PfRule::CNF_EQUIV_POS1:{
		return addVeriTStep(res,VeriTRule::EQUIV_POS2,children,{},*cdp);
	}
  // ======== CNF Equiv Pos version 2
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (not (= F1 F2)) F1 (not F2))	
	// 
	// proof rule: equiv_pos1 
	// proof term: (or (not (= F1 F2)) F1 (not F2))	
	// premises: ()
	// args: ()
	case PfRule::CNF_EQUIV_POS2:{
		return addVeriTStep(res,VeriTRule::EQUIV_POS1,children,{},*cdp);
	}
  // ======== CNF Equiv Neg version 1
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (= F1 F2) F1 F2)	
	// 
	// proof rule: equiv_neg2 
	// proof term: (or (= F1 F2) F1 F2)
	// premises: ()
	// args: ()
	case PfRule::CNF_EQUIV_NEG1:{
		return addVeriTStep(res,VeriTRule::EQUIV_NEG2,children,{},*cdp);
	}
  // ======== CNF Equiv Neg version 2
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (= F1 F2) (not F1) (not F2))	
	// 
	// proof rule: equiv_neg1 
	// proof term: (or (= F1 F2) (not F1) (not F2))
	// premises: ()
	// args: ()
	case PfRule::CNF_EQUIV_NEG2:{
		return addVeriTStep(res,VeriTRule::EQUIV_NEG1,children,{},*cdp);
	}
  // ======== CNF Xor Pos version 1
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (not (xor F1 F2)) F1 F2)	
	// 
	// proof rule: xor_pos1 
	// proof term: (or (not (xor F1 F2)) F1 F2)
	// premises: ()
	// args: ()
	case PfRule::CNF_XOR_POS1:{
		return addVeriTStep(res,VeriTRule::XOR_POS1,children,{},*cdp);
	}
  // ======== CNF Xor Pos version 2
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))	
	// 
	// proof rule: xor_pos2 
	// proof term: (or (not (xor F1 F2)) (not F1) (not F2))
	// premises: ()
	// args: ()
	case PfRule::CNF_XOR_POS2:{
		return addVeriTStep(res,VeriTRule::XOR_POS2,children,{},*cdp);
	}
  // ======== CNF Xor Neg version 1
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (xor F1 F2) (not F1) F2)	
	// 
	// proof rule: xor_neg2 
	// proof term: (or (xor F1 F2) (not F1) F2)
	// premises: ()
	// args: ()
	case PfRule::CNF_XOR_NEG1:{
		return addVeriTStep(res,VeriTRule::XOR_NEG2,children,{},*cdp);
	}
  // ======== CNF Xor Neg version 2
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (xor F1 F2) F1 (not F2))	
	// 
	// proof rule: xor_neg1 
	// proof term: (or (xor F1 F2) F1 (not F2))
	// premises: ()
	// args: ()
	case PfRule::CNF_XOR_NEG2:{
		return addVeriTStep(res,VeriTRule::XOR_NEG1,children,{},*cdp);
	}
  // ======== CNF ITE Pos version 1
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (not (ite C F1 F2)) (not C) F1)	
	// 
	// proof rule: ite_pos2  
	// proof term: (or (not (ite C F1 F2)) (not C) F1)
	// premises: ()
	// args: ()
	case PfRule::CNF_ITE_POS1:{
		return addVeriTStep(res,VeriTRule::ITE_POS2,children,{},*cdp);
	}
  // ======== CNF ITE Pos version 2
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (not (ite C F1 F2)) C F2)	
	// 
	// proof rule: ite_pos1 
	// proof term: (or (not (ite C F1 F2)) C F2)
	// premises: ()
	// args: ()
	case PfRule::CNF_ITE_POS2:{
		return addVeriTStep(res,VeriTRule::ITE_POS1,children,{},*cdp);
	}
  // ======== CNF ITE Pos version 3
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (not (ite C F1 F2)) F1 F2)	
	// 
	// proof rule: ite_pos1
	// proof term: (VP1:(or (not (ite C F1 F2)) C F2))
	// premises: ()
	// args: ()
	//
	// proof rule: ite_pos2
	// proof term: (VP2:(or (not (ite C F1 F2)) (not C) F1))
	// premises: ()
	// args: ()
	//
	// proof rule: resolution
	// proof term: (VP3:(or (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
	// premises: (VP1:(or (not (ite C F1 F2)) C F2)) (VP2:(or (not (ite C F1 F2)) (not C) F1))
	// args: ()
	//
	// proof rule: duplicate_literals
	// proof term: (or (not (ite C F1 F2)) F1 F2)	
	// premises: (VP3:(or (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
	// args: ()
	case PfRule::CNF_ITE_POS3:{ 		
		Node vp1 = d_nm->mkNode(kind::OR,res[0],args[0][0],res[2]);
 		addVeriTStep(vp1,VeriTRule::ITE_POS1,{},{},*cdp);		

		Node vp2 = d_nm->mkNode(kind::OR,res[0],d_nm->mkNode(kind::NOT,args[0][0]),res[1]);	
		addVeriTStep(vp2,VeriTRule::ITE_POS2,{},{},*cdp);

		Node vp3 = d_nm->mkNode(kind::OR,res[0],res[1],res[0],res[2]);//TODO: Find out ordering after resolution
	  addVeriTStep(vp3,VeriTRule::RESOLUTION,{vp1,vp2},{},*cdp);

		addVeriTStep(res,VeriTRule::DUPLICATE_LITERALS,{vp3},{},*cdp);
		return true;
	}
  // ======== CNF ITE Neg version 1
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (ite C F1 F2) (not C) (not F1))	
	// 
	// proof rule: ite_neg2 
	// proof term: (or (ite C F1 F2) (not C) (not F1))
	// premises: ()
	// args: ()	
	case PfRule::CNF_ITE_NEG1:{
		return addVeriTStep(res,VeriTRule::ITE_NEG2,children,{},*cdp);
	}
  // ======== CNF ITE Neg version 2
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (ite C F1 F2) C (not F2))	
	// 
	// proof rule: ite_neg1 
	// proof term: (or (ite C F1 F2) C (not F2))
	// premises: ()
	// args: ()	
	case PfRule::CNF_ITE_NEG2:{
		return addVeriTStep(res,VeriTRule::ITE_NEG1,children,{},*cdp);
	}
  // ======== CNF ITE Neg version 3
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (ite C F1 F2) (not F1) (not F2))	
	// 
	// proof rule: ite_neg1
	// proof term: (VP1:(or (ite C F1 F2) C (not F2)))
	// premises: ()
	// args: ()	
	//
	// proof rule: ite_neg2
	// proof term: (VP2:(or (ite C F1 F2) (not C) (not F1)))
	// premises: ()
	// args: ()
	//
	// proof rule: resolution
	// proof term: (VP3:(or (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
	// premises: ((VP1:(or (ite C F1 F2) C (not F2))) (VP2:(or (ite C F1 F2) (not C) (not F1))))
	// args: ()
	//
	// proof rule: duplicate_literals
	// proof term: (or (ite C F1 F2) C (not F2))
	// premises: (VP3:(or (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
	// args: ()
	case PfRule::CNF_ITE_NEG3:{//TODO
		Node vp1 = d_nm->mkNode(kind::OR,res[0],args[0][0],res[2]);
 		addVeriTStep(vp1,VeriTRule::ITE_NEG1,{},{},*cdp);		

		Node vp2 = d_nm->mkNode(kind::OR,res[0],d_nm->mkNode(kind::NOT,args[0][0]),res[1]);	
		addVeriTStep(vp2,VeriTRule::ITE_NEG2,{},{},*cdp);

		Node vp3 = d_nm->mkNode(kind::OR,res[0],res[1],res[0],res[2]);//TODO: Find out ordering after resolution
	  addVeriTStep(vp3,VeriTRule::RESOLUTION,{vp1,vp2},{},*cdp);

		addVeriTStep(res,VeriTRule::DUPLICATE_LITERALS,{vp3},{},*cdp);
		return true;
	}



	case PfRule::CONG:{
		return addVeriTStep(res,VeriTRule::CONG,children,{},*cdp);
	}

	default:
		return addVeriTStep(res,VeriTRule::UNDEFINED,children,args,*cdp);
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
