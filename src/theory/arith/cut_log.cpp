/*********************                                                        */
/*! \file cut_log.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <cmath>
#include <limits.h>
#include <map>
#include <math.h>

#include "base/output.h"
#include "cvc4autoconfig.h"
#include "theory/arith/approx_simplex.h"
#include "theory/arith/constraint.h"
#include "theory/arith/cut_log.h"
#include "theory/arith/normal_form.h"
#include "util/ostream_util.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

NodeLog::const_iterator NodeLog::begin() const { return d_cuts.begin(); }
NodeLog::const_iterator NodeLog::end() const { return d_cuts.end(); }

NodeLog& TreeLog::getNode(int nid) {
  ToNodeMap::iterator i = d_toNode.find(nid);
  Assert(i != d_toNode.end());
  return (*i).second;
}

TreeLog::const_iterator TreeLog::begin() const { return d_toNode.begin(); }
TreeLog::const_iterator TreeLog::end() const { return d_toNode.end(); }

int TreeLog::getExecutionOrd(){
  int res = next_exec_ord;
  ++next_exec_ord;
  return res;
}
void TreeLog::makeInactive(){  d_active = false; }
void TreeLog::makeActive(){  d_active = true; }
bool TreeLog::isActivelyLogging() const { return d_active; }


PrimitiveVec::PrimitiveVec()
  : len(0)
  , inds(NULL)
  , coeffs(NULL)
{}

PrimitiveVec::~PrimitiveVec(){
  clear();
}
bool PrimitiveVec::initialized() const {
  return inds != NULL;
}
void PrimitiveVec::clear() {
  if(initialized()){
    delete[] inds;
    delete[] coeffs;
    len = 0;
    inds = NULL;
    coeffs = NULL;
  }
}
void PrimitiveVec::setup(int l){
  Assert(!initialized());
  len = l;
  inds = new int[1+len];
  coeffs = new double[1+len];
}
void PrimitiveVec::print(std::ostream& out) const{
  Assert(initialized());
  StreamFormatScope scope(out);

  out << len << " " << std::setprecision(15);
  for(int i = 1; i <= len; ++i){
    out << "["<< inds[i] <<", " << coeffs[i]<<"]";
  }
}
std::ostream& operator<<(std::ostream& os, const PrimitiveVec& pv){
  pv.print(os);
  return os;
}

CutInfo::CutInfo(CutInfoKlass kl, int eid, int o)
    : d_klass(kl),
      d_execOrd(eid),
      d_poolOrd(o),
      d_cutType(kind::UNDEFINED_KIND),
      d_cutRhs(),
      d_cutVec(),
      d_mAtCreation(-1),
      d_rowId(-1),
      d_exactPrecision(nullptr),
      d_explanation(nullptr)
{}

CutInfo::~CutInfo(){
}

int CutInfo::getId() const {
  return d_execOrd;
}

int CutInfo::getRowId() const{
  return d_rowId;
}

void CutInfo::setRowId(int rid){
  d_rowId = rid;
}

void CutInfo::print(ostream& out) const{
  out << "[CutInfo " << d_execOrd << " " << d_poolOrd
      << " " << d_klass << " " << d_cutType << " " << d_cutRhs
      << " ";
  d_cutVec.print(out);
  out << "]" << endl;
}

PrimitiveVec& CutInfo::getCutVector(){
  return d_cutVec;
}

const PrimitiveVec& CutInfo::getCutVector() const{
  return d_cutVec;
}

// void CutInfo::init_cut(int l){
//   cut_vec.setup(l);
// }

Kind CutInfo::getKind() const{
  return d_cutType;
}

void CutInfo::setKind(Kind k){
  Assert(k == kind::LEQ || k == kind::GEQ);
  d_cutType = k;
}

double CutInfo::getRhs() const{
  return d_cutRhs;
}

void CutInfo::setRhs(double r){
  d_cutRhs = r;
}

bool CutInfo::reconstructed() const { return d_exactPrecision != nullptr; }

CutInfoKlass CutInfo::getKlass() const{
  return d_klass;
}

int CutInfo::poolOrdinal() const{
  return d_poolOrd;
}

void CutInfo::setDimensions(int N, int M){
  d_mAtCreation = M;
  d_N = N;
}

int CutInfo::getN() const{
  return d_N;
}

int CutInfo::getMAtCreation() const{
  return d_mAtCreation;
}

/* Returns true if the cut has an explanation. */
bool CutInfo::proven() const { return d_explanation != nullptr; }

bool CutInfo::operator<(const CutInfo& o) const{
  return d_execOrd < o.d_execOrd;
}


void CutInfo::setReconstruction(const DenseVector& ep){
  Assert(!reconstructed());
  d_exactPrecision.reset(new DenseVector(ep));
}

void CutInfo::setExplanation(const ConstraintCPVec& ex){
  Assert(reconstructed());
  if (d_explanation == nullptr)
  {
    d_explanation.reset(new ConstraintCPVec(ex));
  }
  else
  {
    *d_explanation = ex;
  }
}

void CutInfo::swapExplanation(ConstraintCPVec& ex){
  Assert(reconstructed());
  Assert(!proven());
  if (d_explanation == nullptr)
  {
    d_explanation.reset(new ConstraintCPVec());
  }
  d_explanation->swap(ex);
}

const DenseVector& CutInfo::getReconstruction() const {
  Assert(reconstructed());
  return *d_exactPrecision;
}

void CutInfo::clearReconstruction(){
  if(proven()){
    d_explanation = nullptr;
  }

  if(reconstructed()){
    d_exactPrecision = nullptr;
  }

  Assert(!reconstructed());
  Assert(!proven());
}

const ConstraintCPVec& CutInfo::getExplanation() const {
  Assert(proven());
  return *d_explanation;
}

std::ostream& operator<<(std::ostream& os, const CutInfo& ci){
  ci.print(os);
  return os;
}

std::ostream& operator<<(std::ostream& out, CutInfoKlass kl){
  switch(kl){
  case MirCutKlass:
    out << "MirCutKlass"; break;
  case GmiCutKlass:
    out << "GmiCutKlass"; break;
  case BranchCutKlass:
    out << "BranchCutKlass"; break;
  case RowsDeletedKlass:
    out << "RowDeletedKlass"; break;
  case UnknownKlass:
    out << "UnknownKlass"; break;
  default:
    out << "unexpected CutInfoKlass"; break;
  }
  return out;
}
bool NodeLog::isBranch() const{
  return d_brVar >= 0;
}

NodeLog::NodeLog()
  : d_nid(-1)
  , d_parent(NULL)
  , d_tl(NULL)
  , d_cuts()
  , d_rowIdsSelected()
  , d_stat(Open)
  , d_brVar(-1)
  , d_brVal(0.0)
  , d_downId(-1)
  , d_upId(-1)
  , d_rowId2ArithVar()
{}

NodeLog::NodeLog(TreeLog* tl, int node, const RowIdMap& m)
  : d_nid(node)
  , d_parent(NULL)
  , d_tl(tl)
  , d_cuts()
  , d_rowIdsSelected()
  , d_stat(Open)
  , d_brVar(-1)
  , d_brVal(0.0)
  , d_downId(-1)
  , d_upId(-1)
  , d_rowId2ArithVar(m)
{}

NodeLog::NodeLog(TreeLog* tl, NodeLog* parent, int node)
  : d_nid(node)
  , d_parent(parent)
  , d_tl(tl)
  , d_cuts()
  , d_rowIdsSelected()
  , d_stat(Open)
  , d_brVar(-1)
  , d_brVal(0.0)
  , d_downId(-1)
  , d_upId(-1)
  , d_rowId2ArithVar()
{}

NodeLog::~NodeLog(){
  CutSet::iterator i = d_cuts.begin(), iend = d_cuts.end();
  for(; i != iend; ++i){
    CutInfo* c = *i;
    delete c;
  }
  d_cuts.clear();
  Assert(d_cuts.empty());
}

std::ostream& operator<<(std::ostream& os, const NodeLog& nl){
  nl.print(os);
  return os;
}

void NodeLog::copyParentRowIds() {
  Assert(d_parent != NULL);
  d_rowId2ArithVar = d_parent->d_rowId2ArithVar;
}

int NodeLog::branchVariable() const {
  return d_brVar;
}
double NodeLog::branchValue() const{
  return d_brVal;
}
int NodeLog::getNodeId() const {
  return d_nid;
}
int NodeLog::getDownId() const{
  return d_downId;
}
int NodeLog::getUpId() const{
  return d_upId;
}
void NodeLog::addSelected(int ord, int sel){
  Assert(d_rowIdsSelected.find(ord) == d_rowIdsSelected.end());
  d_rowIdsSelected[ord] = sel;
  Debug("approx::nodelog") << "addSelected("<< ord << ", "<< sel << ")" << endl;
}
void NodeLog::applySelected() {
  CutSet::iterator iter = d_cuts.begin(), iend = d_cuts.end(), todelete;
  while(iter != iend){
    CutInfo* curr = *iter;
    int poolOrd = curr->poolOrdinal();
    if(curr->getRowId() >= 0 ){
      // selected previously, kip
      ++iter;
    }else if(curr->getKlass() == RowsDeletedKlass){
      // skip
      ++iter;
    }else if(curr->getKlass() == BranchCutKlass){
      // skip
      ++iter;
    }else if(d_rowIdsSelected.find(poolOrd) == d_rowIdsSelected.end()){
      todelete = iter;
      ++iter;
      d_cuts.erase(todelete);
      delete curr;
    }else{
      Debug("approx::nodelog") << "applySelected " << curr->getId() << " " << poolOrd << "->" << d_rowIdsSelected[poolOrd] << endl;
      curr->setRowId( d_rowIdsSelected[poolOrd] );
      ++iter;
    }
  }
  d_rowIdsSelected.clear();
}

void NodeLog::applyRowsDeleted(const RowsDeleted& rd) {
  std::map<int, CutInfo*> currInOrd; //sorted

  const PrimitiveVec& cv = rd.getCutVector();
  std::vector<int> sortedRemoved (cv.inds+1, cv.inds+cv.len+1);
  sortedRemoved.push_back(INT_MAX);
  std::sort(sortedRemoved.begin(), sortedRemoved.end());

  if(Debug.isOn("approx::nodelog")){
    Debug("approx::nodelog") << "Removing #" << sortedRemoved.size()<< "...";
    for(unsigned k = 0; k<sortedRemoved.size(); k++){
      Debug("approx::nodelog") << ", " << sortedRemoved[k];
    }
    Debug("approx::nodelog") << endl;
    Debug("approx::nodelog") << "cv.len" << cv.len  << endl;
  }

  int min = sortedRemoved.front();

  CutSet::iterator iter = d_cuts.begin(), iend = d_cuts.end();
  while(iter != iend){
    CutInfo* curr= *iter;
    if(curr->getId() < rd.getId()){
      if(d_rowId2ArithVar.find(curr->getRowId()) != d_rowId2ArithVar.end()){
        if(curr->getRowId() >= min){
          currInOrd.insert(make_pair(curr->getRowId(), curr));
        }
      }
    }
    ++iter;
  }

  RowIdMap::const_iterator i, end;
  i=d_rowId2ArithVar.begin(), end = d_rowId2ArithVar.end();
  for(; i != end; ++i){
    int key = (*i).first;
    if(key >= min){
      if(currInOrd.find(key) == currInOrd.end()){
        CutInfo* null = NULL;
        currInOrd.insert(make_pair(key, null));
      }
    }
  }



  std::map<int, CutInfo*>::iterator j, jend;

  int posInSorted = 0;
  for(j = currInOrd.begin(), jend=currInOrd.end(); j!=jend; ++j){
    int origOrd = (*j).first;
    ArithVar v = d_rowId2ArithVar[origOrd];
    int headRemovedOrd = sortedRemoved[posInSorted];
    while(headRemovedOrd < origOrd){
      ++posInSorted;
      headRemovedOrd  = sortedRemoved[posInSorted];
    }
    // headRemoveOrd >= origOrd
    Assert(headRemovedOrd >= origOrd);

    CutInfo* ci = (*j).second;
    if(headRemovedOrd == origOrd){

      if(ci == NULL){
        Debug("approx::nodelog") << "deleting from above because of " << rd << endl;
        Debug("approx::nodelog") << "had " << origOrd << " <-> " << v << endl;
        d_rowId2ArithVar.erase(origOrd);
      }else{
        Debug("approx::nodelog") << "deleting " << ci << " because of " << rd << endl;
        Debug("approx::nodelog") << "had " << origOrd << " <-> " << v << endl;
        d_rowId2ArithVar.erase(origOrd);
        ci->setRowId(-1);
      }
    }else{
      Assert(headRemovedOrd > origOrd);
      // headRemoveOrd > origOrd
      int newOrd = origOrd - posInSorted;
      Assert(newOrd > 0);
      if(ci == NULL){
        Debug("approx::nodelog") << "shifting above down due to " << rd << endl;
        Debug("approx::nodelog") << "had " << origOrd << " <-> " << v << endl;
        Debug("approx::nodelog") << "now have " << newOrd << " <-> " << v << endl;
        d_rowId2ArithVar.erase(origOrd);
        mapRowId(newOrd, v);
      }else{
        Debug("approx::nodelog") << "shifting " << ci << " down due to " << rd << endl;
        Debug("approx::nodelog") << "had " << origOrd << " <-> " << v << endl;
        Debug("approx::nodelog") << "now have " << newOrd << " <-> " << v << endl;
        ci->setRowId(newOrd);
        d_rowId2ArithVar.erase(origOrd);
        mapRowId(newOrd, v);
      }
    }
  }

}

// void NodeLog::adjustRowId(CutInfo& ci, const RowsDeleted& rd) {
//   int origRowId = ci.getRowId();
//   int newRowId = ci.getRowId();
//   ArithVar v = d_rowId2ArithVar[origRowId];

//   const PrimitiveVec& cv = rd.getCutVector();

//   for(int j = 1, N = cv.len; j <= N; j++){
//     int ind = cv.inds[j];
//     if(ind == origRowId){
//       newRowId = -1;
//       break;
//     }else if(ind < origRowId){
//       newRowId--;
//     }
//   }

//   if(newRowId < 0){
//     cout << "deleting " << ci << " because of " << rd << endl;
//     cout << "had " << origRowId << " <-> " << v << endl;
//     d_rowId2ArithVar.erase(origRowId);
//     ci.setRowId(-1);
//   }else if(newRowId != origRowId){
//     cout << "adjusting " << ci << " because of " << rd << endl;
//     cout << "had " << origRowId << " <-> " << v << endl;
//     cout << "now have " << newRowId << " <-> " << v << endl;
//     d_rowId2ArithVar.erase(origRowId);
//     ci.setRowId(newRowId);
//     mapRowId(newRowId, v);
//   }else{
//     cout << "row id unchanged " << ci << " because of " << rd << endl;
//   }
// }


ArithVar NodeLog::lookupRowId(int rowId) const{
  RowIdMap::const_iterator i = d_rowId2ArithVar.find(rowId);
  if(i == d_rowId2ArithVar.end()){
    return ARITHVAR_SENTINEL;
  }else{
    return (*i).second;
  }
}

void NodeLog::mapRowId(int rowId, ArithVar v){
  Assert(lookupRowId(rowId) == ARITHVAR_SENTINEL);
  Debug("approx::nodelog")
    << "On " << getNodeId()
    << " adding row id " << rowId << " <-> " << v << endl;
  d_rowId2ArithVar[rowId] = v;
}



void NodeLog::addCut(CutInfo* ci){
  Assert(ci != NULL);
  d_cuts.insert(ci);
}

void NodeLog::print(ostream& o) const{
  o << "[n" << getNodeId();
  for(const_iterator iter = begin(), iend = end(); iter != iend; ++iter ){
    CutInfo* cut = *iter;
    o << ", " << cut->poolOrdinal();
    if(cut->getRowId() >= 0){
      o << " " << cut->getRowId();
    }
  }
  o << "]" << std::endl;
}

void NodeLog::closeNode(){
  Assert(d_stat == Open);
  d_stat = Closed;
}

void NodeLog::setBranch(int br, double val, int d, int u){
  Assert(d_stat == Open);
  d_brVar = br;
  d_brVal = val;
  d_downId = d;
  d_upId = u;
  d_stat = Branched;
}

TreeLog::TreeLog()
  : next_exec_ord(0)
  , d_toNode()
  , d_branches()
  , d_numCuts(0)
  , d_active(false)
{
  NodeLog::RowIdMap empty;
  reset(empty);
}

int TreeLog::getRootId() const{
  return 1;
}

NodeLog& TreeLog::getRootNode(){
  return getNode(getRootId());
}

void TreeLog::clear(){
  next_exec_ord = 0;
  d_toNode.clear();
  d_branches.purge();

  d_numCuts = 0;

  // add root
}

void TreeLog::reset(const NodeLog::RowIdMap& m){
  clear();
  d_toNode.insert(make_pair(getRootId(), NodeLog(this, getRootId(), m)));
}

void TreeLog::addCut(){ d_numCuts++; }
uint32_t TreeLog::cutCount() const { return d_numCuts; }
void TreeLog::logBranch(uint32_t x){
  d_branches.add(x);
}
uint32_t TreeLog::numBranches(uint32_t x){
  return d_branches.count(x);
}

void TreeLog::branch(int nid, int br, double val, int dn, int up){
  NodeLog& nl = getNode(nid);
  nl.setBranch(br, val, dn, up);

  d_toNode.insert(make_pair(dn, NodeLog(this, &nl, dn)));
  d_toNode.insert(make_pair(up, NodeLog(this, &nl, up)));
}

void TreeLog::close(int nid){
  NodeLog& nl = getNode(nid);
  nl.closeNode();
}



// void TreeLog::applySelected() {
//   std::map<int, NodeLog>::iterator iter, end;
//   for(iter = d_toNode.begin(), end = d_toNode.end(); iter != end; ++iter){
//     NodeLog& onNode = (*iter).second;
//     //onNode.applySelected();
//   }
// }

void TreeLog::print(ostream& o) const{
  o << "TreeLog: " << d_toNode.size() << std::endl;
  for(const_iterator iter = begin(), iend = end(); iter != iend; ++iter){
    const NodeLog& onNode = (*iter).second;
    onNode.print(o);
  }
}

void TreeLog::applyRowsDeleted(int nid, const RowsDeleted& rd){
  NodeLog& nl = getNode(nid);
  nl.applyRowsDeleted(rd);
}

void TreeLog::mapRowId(int nid, int ind, ArithVar v){
  NodeLog& nl = getNode(nid);
  nl.mapRowId(ind, v);
}

void DenseVector::purge() {
  lhs.purge();
  rhs = Rational(0);
}

RowsDeleted::RowsDeleted(int execOrd, int nrows, const int num[])
  : CutInfo(RowsDeletedKlass, execOrd, 0)
{
  d_cutVec.setup(nrows);
  for(int j=1; j <= nrows; j++){
    d_cutVec.coeffs[j] = 0;
    d_cutVec.inds[j] = num[j];
  }
}

BranchCutInfo::BranchCutInfo(int execOrd, int br, Kind dir, double val)
  : CutInfo(BranchCutKlass, execOrd, 0)
{
  d_cutVec.setup(1);
  d_cutVec.inds[1] = br;
  d_cutVec.coeffs[1] = +1.0;
  d_cutRhs = val;
  d_cutType = dir;
}

void TreeLog::printBranchInfo(ostream& os) const{
  uint32_t total = 0;
  DenseMultiset::const_iterator iter = d_branches.begin(),  iend = d_branches.end();
  for(; iter != iend; ++iter){
    uint32_t el = *iter;
    total += el;
  }
  os << "printBranchInfo() : " << total << endl;
  iter = d_branches.begin(),  iend = d_branches.end();
  for(; iter != iend; ++iter){
    uint32_t el = *iter;
    os << "["<<el <<", " << d_branches.count(el) << "]";
  }
  os << endl;
}


void DenseVector::print(std::ostream& os) const {
  os << rhs << " + ";
  print(os, lhs);
}
void DenseVector::print(ostream& out, const DenseMap<Rational>& v){
  out << "[DenseVec len " <<  v.size();
  DenseMap<Rational>::const_iterator iter, end;
  for(iter = v.begin(), end = v.end(); iter != end; ++iter){
    ArithVar x = *iter;
    out << ", "<< x << " " << v[x];
  }
  out << "]";
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
