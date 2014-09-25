/*********************                                                        */
/*! \file rewriter_proof.cpp
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "proof/rewriter_proof.h"

using namespace CVC4;

RewriterProof::RewriterProof()
  : d_rewriteMap()
{}

void RewriterProof::registerRewrite(Expr from, Expr to, RewriteTag tag) {
  Assert (d_rewriteMap.find(from) == d_rewriteMap.end());
  d_rewriteMap[from] = RewriteRule(tag, from, to);
}

RewriteRule RewriterProof::getRewrite(Expr from) {
  RewriteMap::const_iterator it = d_rewriteMap.find(from);
  Assert (it != d_rewriteMap.end());
  return it->second;
}

RewriteId RewriterProof::getRewriteId(Expr from) {
  RewriteMap::const_iterator it = d_rewriteMap.find(from);
  Assert (it != d_rewriteMap.end());
  return it->second.id;
}

void RewriterProof::finalizeRewriteProof(Expr from, RewriteStack& stack) {
  
}

void RewriterProof::finalizeRewriteProof(Expr from, RewriteStack& stack) {
  if (hasRewriteRule(from)) {
    RewriteRule& rwr = getRewrite(from);
    Expr to = rwr.to;
    RewriteTag tag = rewr.tag;
    Assert (from == rwr.from);
    stack.push_back(rwr);
  }
}


std::string LFSCRewriterProof::toLFSCRewriteName(RewriteRule& rw) {
  switch(rw) {
  case BvXorZero:
    return "bv_xor_zero";
  case BvXorOne:
    return "bv_xor_one";
  case BvNotIdemp:
    return "bv_not_idemp";
  case BVNorEliminate:
    return "bv_nor_eliminate";
  }
  
  Unreachable("Unknown rewrite rule", rw);
}

