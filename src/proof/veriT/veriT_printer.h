/*********************                                                        */
/*! \file veriT_printer.h
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

#include <memory>
#include "cvc4_private.h"
#include "expr/proof_node_updater.h"
#include "proof/veriT/veriT_proof_rule.cpp"

#ifndef CVC4__PROOF__VERIT_PROOF_PRINTER_H
#define CVC4__PROOF__VERIT_PROOF_PRINTER_H

#include<iostream>

//TODO:delete
#include<string>

namespace CVC4 {

namespace proof {



//TODO: Delete, temp ad-hoc code to test conversion
//There are cases when the childrens are not the premises? If that is true change this code
static int veriTPrintInternal(std::ostream& out,
															 std::shared_ptr<ProofNode> pfn, int i){
	int temp = i;
	std::vector<int> childIds;
  i++;
  
	std::string last_step;
	if (static_cast<VeriTRule>(std::stoul(pfn->getArguments()[0].toString())) == VeriTRule::ANCHOR){
		out << "(anchor :step " << last_step << ":args ";
		for (int i = 2; i < pfn->getArguments().size();i++){
			out << " " << pfn->getArguments()[i];
		}
		out << ")\n";
	}
	
	for(auto child: pfn->getChildren()){
		childIds.push_back(i);
		i = veriTPrintInternal(out,child,i);
	}
  
 	last_step = i;

	if (static_cast<VeriTRule>(std::stoul(pfn->getArguments()[0].toString())) == VeriTRule::ASSUME){
		out << "(assume t" << temp << " " << pfn->getArguments()[1] << ")" << std::endl;
		return i;
	}

	if (static_cast<VeriTRule>(std::stoul(pfn->getArguments()[0].toString())) == VeriTRule::ANCHOR){
		return i;
	}	
		
  if (pfn->getArguments().size() == 2) {
		out << "(step t" << temp << " " << pfn->getArguments()[1] << " :rule " 
			<< veriTRuletoString(static_cast<VeriTRule>(std::stoul(pfn->getArguments()[0].toString())));
		if(childIds.size()>=1){
			out << " :premises";
			for(auto j : childIds){
				out << " t" << j;
			}
		}
		out << ")\n";
	}
	else if (pfn->getArguments().size() > 2){
		out << "(step t" << temp << " " <<pfn->getArguments()[1] << " :rule " <<  
			veriTRuletoString(static_cast<VeriTRule>(std::stoul(pfn->getArguments()[0].toString())))  << " :args";
		for (int i = 2; i < pfn->getArguments().size();i++){
			out << " " << pfn->getArguments()[i];
		}
		if(childIds.size() >= 1){
		out << " :premises";
		for(auto j : childIds){
			out << " t" << j;
		}
		}
		out << ")\n";
	}
  else{
		out << "Not translated yet\n";
	}
	return i;
}


static void veriTPrinter(std::ostream& out, 
												 std::shared_ptr<ProofNode> pfn)
{
  // should traverse proof node, print each as a proof step, according to the
  // VERIT_RULE id in the veriTRule enum
  	
	out <<"\n";
	out <<"\n";
	out <<"Print VeriT proof: " << std::endl;
	//Do not print outermost scope TODO: replace after SCOPE rule works
	veriTPrintInternal(out,pfn->getChildren()[0],0);
	//For test purposes print outermost scope
  //veriTPrintInternal(out,pfn,0);
	out <<"\n";
}




}

}

#endif
