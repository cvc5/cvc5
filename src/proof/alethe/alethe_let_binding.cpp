/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The implementation of the module for Alethe let binding.
 */

#include "proof/alethe/alethe_let_binding.h"

#include <sstream>

namespace cvc5::internal {

namespace proof {

AletheLetBinding::AletheLetBinding(uint32_t thresh) : LetBinding(thresh) {}

Node AletheLetBinding::convert(Node n, const std::string& prefix)
{
  if (d_letMap.empty())
  {
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  // terms with a child that is being declared
  std::unordered_set<TNode> hasDeclaredChild;
  // For a term being declared, its position relative to the list of children
  // of the parent of this term, its parent, and its declaration value. These
  // are necessary to properly declare letified terms occurring for the first
  // time once conversions start
  std::unordered_map<TNode, size_t> declaredPosition;
  std::unordered_map<TNode, TNode> parentOf;
  std::unordered_map<TNode, Node> declaredValue;
  // visiting utils
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  // start with input
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      uint32_t id = getId(cur);
      // do not letify id 0
      if (id > 0)
      {
        Trace("alethe-printer-share")
            << "Node " << cur << " has id " << id << "\n";
        // if cur has previously been declared, just use the let variable.
        if (d_declared.find(cur) != d_declared.end())
        {
          // create the let variable for cur
          std::stringstream ss;
          ss << prefix << id;
          visited[cur] = nm->mkBoundVar(ss.str(), cur.getType());
          Trace("alethe-printer-share")
              << "\tdeclared, use var " << visited[cur] << "\n";
          continue;
        }
        // If the input of this method is letified and it has not yet been
        // declared, we will need to declare its post-visit result. So we do
        // nothing at this point other than book-keep. The information is
        // necessary to guarentee that this occurence, its first in the overall
        // term, is ultimately used as a declaration rather than as just the
        // letified variable. For this we find the parent of this first
        // occurrence of cur and the position in its children in which cur
        // occurs. The declaration will be created when cur is post-visited and
        // used when the parent of this occurrence of cur is post-visited.
        if (cur != n)
        {
          // The parent of cur will have been set when it was visited
          Assert(parentOf.find(cur) != parentOf.end());
          Node parent = parentOf[cur];
          auto itPos = std::find(parent.begin(), parent.end(), cur);
          Assert(itPos != parent.end());
          declaredPosition[cur] = itPos - parent.begin();
          Trace("alethe-printer-share")
              << "\tset for its parent " << parent << " mark position "
              << itPos - parent.begin() << "\n";
        }
        // Mark that future occurrences are just the variable
        d_declared.insert(cur);
      }
      if (cur.isClosure())
      {
        // We do not convert beneath quantifiers, so we need to finish the
        // traversal here. However if id > 0, then we need to declare cur's
        // variable. Since cur is not post-visited the declaration is of cur
        // itself.
        if (id == 0)
        {
          visited[cur] = cur;
          continue;
        }
        std::stringstream ss;
        ss << "(! ";
        options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
        options::ioutils::applyDagThresh(ss, 0);
        cur.toStream(ss);
        ss << " :named " << prefix << id << ")";
        Node letVar = nm->mkRawSymbol(ss.str(), cur.getType());
        visited[cur] = letVar;
        declaredValue[cur] = letVar;
        continue;
      }
      visited[cur] = Node::null();
      visit.push_back(cur);
      // We now check if any of the children of cur is being declared, in which
      // case we associate cur as the parent of declared children, as will as
      // that cur has declared children.
      //
      // We also use this loop to add the children to be visited. Note we add
      // them in reverse order, since we must do post-order traversal (last
      // added to the list are first visited, thus this entails left-to-right
      // traversal of children)
      for (size_t i = 0, size = cur.getNumChildren(); i < size; ++i)
      {
        visit.push_back(cur[size - i - 1]);
        id = getId(cur[i]);
        if (id > 0 && d_declared.find(cur[i]) == d_declared.end())
        {
          parentOf[cur[i]] = cur;
          hasDeclaredChild.insert(cur);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      uint32_t id;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      // if cur is a parent has declared child, then for each position we must
      // check if that position is of a child being declared and whose declared
      // position is that one. In this case we use not the value in visited but
      // rather the value in declaredValue
      bool checkDeclaredChild = hasDeclaredChild.count(cur);
      if (checkDeclaredChild)
      {
        Trace("alethe-printer-share")
            << "Post-visiting node " << cur << " with declared child\n";
      }
      for (size_t i = 0, size = cur.getNumChildren(); i < size; ++i)
      {
        bool useVisited = true;
        // cur has a declared child and if cur[i] is declared and in this
        // position, then we use its declared value rather than visited[cur[i]].
        if (checkDeclaredChild)
        {
          const auto& itDeclPos = declaredPosition.find(cur[i]);
          useVisited =
              itDeclPos == declaredPosition.end() || itDeclPos->second != i;
        }
        Assert(useVisited || getId(cur[i]) > 0)
            << "With input " << n << " we got child " << cur[i]
            << " to use declared value but its id is 0\n";
        it = useVisited ? visited.find(cur[i]) : declaredValue.find(cur[i]);
        Assert(it != visited.end())
            << "With input " << n << " did not find for term " << cur
            << " its child " << cur[i] << " in map with useVisited "
            << useVisited << "\n";
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      id = getId(cur);
      // if cur has id bigger than 0, then we are declaring its conversion to
      // ret. We save the declaration in declaredValue and set the value in
      // visited to be the let variable, since next occurrences should use that.
      // The use of the declared value will be controlled by the parent. If cur
      // is n, since there is no parent, then we use directly the declared
      // value.
      if (id > 0)
      {
        std::stringstream ss, ssVar;
        ss << "(! ";
        options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
        options::ioutils::applyDagThresh(ss, 0);
        ret.toStream(ss);
        ssVar << prefix << id;
        ss << " :named " << ssVar.str() << ")";
        Node declaration = nm->mkRawSymbol(ss.str(), ret.getType());
        declaredValue[cur] = declaration;
        visited[cur] =
            cur == n ? declaration : nm->mkBoundVar(ssVar.str(), cur.getType());
        continue;
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace proof
}  // namespace cvc5::internal
