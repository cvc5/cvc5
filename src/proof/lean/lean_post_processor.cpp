
#include "../../expr/proof_node_updater.h"
#include "expr/lazy_proof.h"
#include "expr/proof_node_algorithm.h"
#include "proof/lean/lean_post_processor.h"

namespace CVC4 {

namespace proof {

  LeanProofPostprocessCallback::LeanProofPostprocessCallback(ProofNodeManager* pnm) : d_pnm(pnm) {}

  LeanProofPostprocess::LeanProofPostprocess(ProofNodeManager* pnm)
    : d_cb(LeanProofPostprocessCallback(pnm)),
      d_pnm(pnm) {}

  bool LeanProofPostprocessCallback::shouldUpdate(ProofNode* pn){
    return false;
  };

  bool LeanProofPostprocessCallback::update(
                Node res,
                PfRule id,
                const std::vector<Node>& children,
                const std::vector<Node>& args,
                CDProof* cdp,
                bool& continueUpdate)
    {
      return true;
    };

  void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf) {};

}
}
