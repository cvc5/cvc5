/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference information utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__INFER_INFO_H
#define CVC4__THEORY__STRINGS__INFER_INFO_H

#include "expr/node.h"
#include <map>
#include <vector>

namespace CVC4 {
namespace theory {
namespace strings {


/** Types of inferences used in the procedure
 *
 * These are variants of the inference rules in Figures 3-5 of Liang et al.
 * "A DPLL(T) Solver for a Theory of Strings and Regular Expressions", CAV 2014.
 */
enum Inference
{
  INFER_NONE,
  // string split constant propagation, for example:
  //     x = y, x = "abc", y = y1 ++ "b" ++ y2
  //       implies y1 = "a" ++ y1'
  INFER_SSPLIT_CST_PROP,
  // string split variable propagation, for example:
  //     x = y, x = x1 ++ x2, y = y1 ++ y2, len( x1 ) >= len( y1 )
  //       implies x1 = y1 ++ x1'
  // This is inspired by Zheng et al CAV 2015.
  INFER_SSPLIT_VAR_PROP,
  // length split, for example:
  //     len( x1 ) = len( y1 ) V len( x1 ) != len( y1 )
  // This is inferred when e.g. x = y, x = x1 ++ x2, y = y1 ++ y2.
  INFER_LEN_SPLIT,
  // length split empty, for example:
  //     z = "" V z != ""
  // This is inferred when, e.g. x = y, x = z ++ x1, y = y1 ++ z
  INFER_LEN_SPLIT_EMP,
  // string split constant binary, for example:
  //     x1 = "aaaa" ++ x1' V "aaaa" = x1 ++ x1'
  // This is inferred when, e.g. x = y, x = x1 ++ x2, y = "aaaaaaaa" ++ y2.
  // This inference is disabled by default and is enabled by stringBinaryCsp().
  INFER_SSPLIT_CST_BINARY,
  // string split constant
  //    x = y, x = "c" ++ x2, y = y1 ++ y2, y1 != ""
  //      implies y1 = "c" ++ y1'
  // This is a special case of F-Split in Figure 5 of Liang et al CAV 2014.
  INFER_SSPLIT_CST,
  // string split variable, for example:
  //    x = y, x = x1 ++ x2, y = y1 ++ y2
  //      implies x1 = y1 ++ x1' V y1 = x1 ++ y1'
  // This is rule F-Split in Figure 5 of Liang et al CAV 2014.
  INFER_SSPLIT_VAR,
  // flat form loop, for example:
  //    x = y, x = x1 ++ z, y = z ++ y2
  //      implies z = u2 ++ u1, u in ( u1 ++ u2 )*, x1 = u2 ++ u, y2 = u ++ u1
  //        for fresh u, u1, u2.
  // This is the rule F-Loop from Figure 5 of Liang et al CAV 2014.
  INFER_FLOOP,
};
std::ostream& operator<<(std::ostream& out, Inference i);  
  
/** 
 * Length status, used for indicating the length constraints for Skolems
 * introduced by the theory of strings.
 */
enum LengthStatus
{
  LENGTH_SPLIT,
  LENGTH_ONE,
  LENGTH_GEQ_ONE
};

class InferInfo
{
 public:
  /** for debugging
    *
    * The base pair of strings d_i/d_j that led to the inference, and whether
    * (d_rev) we were processing the normal forms of these strings in reverse
    * direction.
    */
  Node d_i;
  Node d_j;
  bool d_rev;
  std::vector<Node> d_ant;
  std::vector<Node> d_antn;
  std::map<LengthStatus, std::vector<Node> > d_new_skolem;
  Node d_conc;
  Inference d_id;
  std::map<Node, bool> d_pending_phase;
  unsigned d_index;
  Node d_nf_pair[2];
  bool sendAsLemma();
};


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
