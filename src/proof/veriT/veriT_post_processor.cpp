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
	//For now translate all.`
  /*switch(pn->getRule()){
    case PfRule::REFL: return false;
		case PfRule::TRANS: return false;
  }*/
	if(pn->getRule() == PfRule::VERIT_RULE){
		return false;
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



//TODO: It might be possible to use res.toExpr() to get conclusion	
switch(id){
	//Assumes are ultimately not printed at this place as they are already occur as XY veriT rules 
	//(see update of SCOPE rule). But the: printer has to know which assumption is needed.  
	case PfRule::ASSUME:{										
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::ASSUME)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;

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
		Node three_neg = nm->mkNode(kind::OR,(args[0].negate().negate().negate(),args[0])); //TODO: it seems negate cannot be used, use mkNode!
		new_args.push_back(three_neg);
		std::cout << three_neg.toExpr() << std::endl;
		cdp->addStep(three_neg,PfRule::VERIT_RULE,children,new_args);

		new_args.clear();
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_NOT)));
		Node four_neg = nm->mkNode(kind::OR,(args[0].negate().negate().negate().negate(),args[0].negate())); 
		new_args.push_back(four_neg);
		cdp->addStep(four_neg,PfRule::VERIT_RULE,{three_neg},new_args);

		new_args.clear();
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,{four_neg,three_neg},new_args);

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
	case PfRule::EQUIV_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::EQUIV1)));
		new_args.push_back(res);	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
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

		new_args.empty();
	  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(res);
		cdp->addStep(res,PfRule::VERIT_RULE,{children[0],n},new_args);
		return true;

	}
	case PfRule::CONTRA:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::RESOLUTION)));
		new_args.push_back(Node::null()); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	case PfRule::AND_ELIM:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::AND)));
		new_args.push_back(res);
		//new_args.push_back(args[0]);
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
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
	case PfRule::NOT_OR_ELIM:{//TODO			
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_OR)));
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
	case PfRule::NOT_XOR_ELIM2:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_XOR1)));
		new_args.push_back(res); 	
		cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
		return true;
	}
	case PfRule::NOT_XOR_ELIM1:{
		new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::NOT_XOR2)));
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
