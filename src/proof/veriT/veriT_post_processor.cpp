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
#include "../../expr/proof_node_updater.h"
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
	//For now translate all.
  switch(pn->getRule()){
    case PfRule::VERIT_RULE:
      return false;
  }
	return true;
} 


bool VeriTProofPostprocessCallback::update(Node res,
				           PfRule id,
				           const std::vector<Node>& children,
				           const std::vector<Node>& args,
				           CDProof* cdp,
				           bool& continueUpdate){

	NodeManager* nm = NodeManager::currentNM();

	std::vector<Node> new_args = std::vector<Node>();
	new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeriTRule::ASSUME))); 
	new_args.push_back(nm->fromExpr(res.toExpr()));	
	new_args.insert(new_args.begin(),args.begin(),args.end());
	cdp->addStep(res,PfRule::VERIT_RULE,children,new_args);
	return true;
}

VeriTProofPostprocess::VeriTProofPostprocess(ProofNodeManager* pnm,ProofNodeUpdaterCallback &cb):ProofNodeUpdater{pnm,cb}{}

VeriTProofPostprocess::~VeriTProofPostprocess(){}

void VeriTProofPostprocess::process(std::shared_ptr<ProofNode> pf){
	ProofNodeUpdater::process(pf);
}


	
	
}

}
