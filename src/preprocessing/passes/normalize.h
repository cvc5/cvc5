/******************************************************************************
 * Top contributors (to current version):
 *   Daneshvar Amrollahi
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Normalizes the input benchmark regardless of the symbol names and assertion order. 
 */

 #include "cvc5_private.h"

 #ifndef CVC5__PREPROCESSING__PASSES__NORMALIZE_H
 #define CVC5__PREPROCESSING__PASSES__NORMALIZE_H
 
 #include "preprocessing/preprocessing_pass.h"
 #include <unordered_map>
 
 namespace cvc5::internal {
 namespace preprocessing {
 namespace passes {
 
 
 
 struct NodeInfo
 {
   Node node;
   std::string encoding;                                   // Compressed string of the DAG
   uint32_t equivClass;                                    // Equivalence class ID
   std::unordered_map<std::string, int32_t> role;          // First occurence index (counter) of each symbol when traversing the DAG. 
   std::vector<std::pair<std::string, int32_t>> varNames;  
   uint32_t id;                                            // Index of the assertion after first round of sorting
 
   NodeInfo() {}
 
   NodeInfo(
     const Node& n, 
     const std::string& enc, 
     uint32_t eqClass,
     const std::unordered_map<std::string, int32_t>& r,
     const std::vector<std::pair<std::string, int32_t>>& vn
   ) : node(n), encoding(enc), equivClass(eqClass), role(r), varNames(vn) {}
 
   void print() const {
     std::cout << "Node : " << node << std::endl;
     std::cout << "Encoding: " << encoding << std::endl;
     std::cout << "Roles: ";
     for (const auto& [symbol, idx] : role)
     {
         std::cout << symbol << " : " << idx << " , ";
     }
     std::cout << std::endl;
     std::cout << "Symbols: ";
     for (const auto& [symbol, idx] : varNames)
     {
         std::cout << symbol << " : " << idx << " , ";
     }
     std::cout << std::endl;
   }
 
   void setId(uint32_t i) { id = i; }
 };
 
 
 
 class Normalize : public PreprocessingPass
 {
  public:
   Normalize(PreprocessingPassContext* preprocContext);
 
  protected:
   PreprocessingPassResult applyInternal(
       AssertionPipeline* assertionsToPreprocess) override;
 
 private:
   struct Statistics
   {
     
     TimerStat d_passTime;
     Statistics(StatisticsRegistry& reg);
   };
  
   std::unique_ptr<NodeInfo> getNodeInfo(const Node& node);
   Statistics d_statistics;
 };
 
 }  // namespace passes
 }  // namespace preprocessing
 }  // namespace cvc5::internal
 
 #endif /* CVC5__PREPROCESSING__PASSES__NORMALIZE_H */
 