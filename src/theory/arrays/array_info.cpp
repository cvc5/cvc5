/*********************                                                        */
/*! \file array_info.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Clark Barrett
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Contains additional classes to store context dependent information
 ** for each term of type array
 **
 **
 **/

#include "theory/arrays/array_info.h"

namespace CVC4 {
namespace theory {
namespace arrays {

bool inList(const CTNodeList* l, const TNode el) {
  CTNodeList::const_iterator it = l->begin();
  for ( ; it!= l->end(); it ++) {
    if(*it == el)
      return true;
  }
  return false;
}

void printList (CTNodeList* list) {
  CTNodeList::const_iterator it = list->begin();
  Trace("arrays-info")<<"   [ ";
  for(; it != list->end(); it++ ) {
    Trace("arrays-info")<<(*it)<<" ";
  }
  Trace("arrays-info")<<"] \n";
}

void printList (List<TNode>* list) {
  List<TNode>::const_iterator it = list->begin();
  Trace("arrays-info")<<"   [ ";
  for(; it != list->end(); it++ ) {
    Trace("arrays-info")<<(*it)<<" ";
  }
  Trace("arrays-info")<<"] \n";
}

void ArrayInfo::mergeLists(CTNodeList* la, const CTNodeList* lb) const{
  std::set<TNode> temp;
  CTNodeList::const_iterator it;
  for(it = la->begin() ; it != la->end(); it++ ) {
    temp.insert((*it));
  }

  for(it = lb->begin() ; it!= lb->end(); it++ ) {
    if(temp.count(*it) == 0) {
      la->push_back(*it);
    }
  }
}

void ArrayInfo::addIndex(const Node a, const TNode i) {
  Assert(a.getType().isArray());
  Assert(!i.getType().isArray()); // temporary for flat arrays

  Trace("arrays-ind")<<"Arrays::addIndex "<<a<<"["<<i<<"]\n";
  CTNodeList* temp_indices;
  Info* temp_info;

  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_indices = new(true) CTNodeList(ct);
    temp_indices->push_back(i);

    temp_info = new Info(ct, bck);
    temp_info->indices = temp_indices;
    info_map[a] = temp_info;
  } else {
    temp_indices = (*it).second->indices;
    if (! inList(temp_indices, i)) {
      temp_indices->push_back(i);
    }
  }
  if(Trace.isOn("arrays-ind")) {
    printList((*(info_map.find(a))).second->indices);
  }

}

void ArrayInfo::addStore(const Node a, const TNode st){
  Assert(a.getType().isArray());
  Assert(st.getKind()== kind::STORE); // temporary for flat arrays

  CTNodeList* temp_store;
  Info* temp_info;

  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_store = new(true) CTNodeList(ct);
    temp_store->push_back(st);

    temp_info = new Info(ct, bck);
    temp_info->stores = temp_store;
    info_map[a]=temp_info;
  } else {
    temp_store = (*it).second->stores;
    if(! inList(temp_store, st)) {
      temp_store->push_back(st);
    }
  }
};


void ArrayInfo::addInStore(const TNode a, const TNode b){
  Trace("arrays-addinstore")<<"Arrays::addInStore "<<a<<" ~ "<<b<<"\n";
  Assert(a.getType().isArray());
  Assert(b.getType().isArray());

  CTNodeList* temp_inst;
  Info* temp_info;

  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_inst = new(true) CTNodeList(ct);
    temp_inst->push_back(b);

    temp_info = new Info(ct, bck);
    temp_info->in_stores = temp_inst;
    info_map[a] = temp_info;
  } else {
    temp_inst = (*it).second->in_stores;
    if(! inList(temp_inst, b)) {
      temp_inst->push_back(b);
    }
  }
};


void ArrayInfo::setNonLinear(const TNode a) {
  Assert(a.getType().isArray());
  Info* temp_info;
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_info = new Info(ct, bck);
    temp_info->isNonLinear = true;
    info_map[a] = temp_info;
  } else {
    (*it).second->isNonLinear = true;
  }
  
}

void ArrayInfo::setRIntro1Applied(const TNode a) {
  Assert(a.getType().isArray());
  Info* temp_info;
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_info = new Info(ct, bck);
    temp_info->rIntro1Applied = true;
    info_map[a] = temp_info;
  } else {
    (*it).second->rIntro1Applied = true;
  }
  
}

void ArrayInfo::setModelRep(const TNode a, const TNode b) {
  Assert(a.getType().isArray());
  Info* temp_info;
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_info = new Info(ct, bck);
    temp_info->modelRep = b;
    info_map[a] = temp_info;
  } else {
    (*it).second->modelRep = b;
  }
  
}

/**
 * Returns the information associated with TNode a
 */

const Info* ArrayInfo::getInfo(const TNode a) const{
  CNodeInfoMap::const_iterator it = info_map.find(a);

  if(it!= info_map.end()) {
      return (*it).second;
  }
  return emptyInfo;
}

const bool ArrayInfo::isNonLinear(const TNode a) const
{
  CNodeInfoMap::const_iterator it = info_map.find(a);

  if(it!= info_map.end()) {
    return (*it).second->isNonLinear;
  }
  return false;
}

const bool ArrayInfo::rIntro1Applied(const TNode a) const
{
  CNodeInfoMap::const_iterator it = info_map.find(a);

  if(it!= info_map.end()) {
    return (*it).second->rIntro1Applied;
  }
  return false;
}

const TNode ArrayInfo::getModelRep(const TNode a) const
{
  CNodeInfoMap::const_iterator it = info_map.find(a);

  if(it!= info_map.end()) {
    return (*it).second->modelRep;
  }
  return TNode();
}

const CTNodeList* ArrayInfo::getIndices(const TNode a) const{
  CNodeInfoMap::const_iterator it = info_map.find(a);
  if(it!= info_map.end()) {
    return (*it).second->indices;
  }
  return emptyList;
}

const CTNodeList* ArrayInfo::getStores(const TNode a) const{
  CNodeInfoMap::const_iterator it = info_map.find(a);
  if(it!= info_map.end()) {
    return (*it).second->stores;
  }
  return emptyList;
}

const CTNodeList* ArrayInfo::getInStores(const TNode a) const{
  CNodeInfoMap::const_iterator it = info_map.find(a);
  if(it!= info_map.end()) {
    return (*it).second->in_stores;
  }
  return emptyList;
}


void ArrayInfo::mergeInfo(const TNode a, const TNode b){
  // can't have assertion that find(b) = a !
  TimerStat::CodeTimer codeTimer(d_mergeInfoTimer);
  ++d_callsMergeInfo;

  Trace("arrays-mergei")<<"Arrays::mergeInfo merging "<<a<<"\n";
  Trace("arrays-mergei")<<"                      and "<<b<<"\n";

  CNodeInfoMap::iterator ita = info_map.find(a);
  CNodeInfoMap::iterator itb = info_map.find(b);

  if(ita != info_map.end()) {
    Trace("arrays-mergei")<<"Arrays::mergeInfo info "<<a<<"\n";
    if(Trace.isOn("arrays-mergei"))
      (*ita).second->print();

    if(itb != info_map.end()) {
      Trace("arrays-mergei")<<"Arrays::mergeInfo info "<<b<<"\n";
      if(Trace.isOn("arrays-mergei"))
        (*itb).second->print();

      CTNodeList* lista_i = (*ita).second->indices;
      CTNodeList* lista_st = (*ita).second->stores;
      CTNodeList* lista_inst = (*ita).second->in_stores;


      CTNodeList* listb_i = (*itb).second->indices;
      CTNodeList* listb_st = (*itb).second->stores;
      CTNodeList* listb_inst = (*itb).second->in_stores;

      mergeLists(lista_i, listb_i);
      mergeLists(lista_st, listb_st);
      mergeLists(lista_inst, listb_inst);

      /* sketchy stats */

      //FIXME
      int s = 0;//lista_i->size();
      d_maxList.maxAssign(s);


      if(s!= 0) {
        d_avgIndexListLength.addEntry(s);
        ++d_listsCount;
      }
      s = lista_st->size();
      d_maxList.maxAssign(s);
      if(s!= 0) {
        d_avgStoresListLength.addEntry(s);
        ++d_listsCount;
      }

      s = lista_inst->size();
      d_maxList.maxAssign(s);
      if(s!=0) {
        d_avgInStoresListLength.addEntry(s);
        ++d_listsCount;
      }

      /* end sketchy stats */

    }

  } else {
    Trace("arrays-mergei")<<" First element has no info \n";
    if(itb != info_map.end()) {
      Trace("arrays-mergei")<<" adding second element's info \n";
      (*itb).second->print();

      CTNodeList* listb_i = (*itb).second->indices;
      CTNodeList* listb_st = (*itb).second->stores;
      CTNodeList* listb_inst = (*itb).second->in_stores;

      Info* temp_info = new Info(ct, bck);

      mergeLists(temp_info->indices, listb_i);
      mergeLists(temp_info->stores, listb_st);
      mergeLists(temp_info->in_stores, listb_inst);
      info_map[a] = temp_info;

    } else {
    Trace("arrays-mergei")<<" Second element has no info \n";
    }

   }
  Trace("arrays-mergei")<<"Arrays::mergeInfo done \n";

}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
