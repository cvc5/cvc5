/*********************                                                        */
/*! \file didyoumean.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief did-you-mean style suggestions.
 **
 ** ``What do you mean? I don't understand.'' An attempt to be more
 ** helpful than that. Similar to one in git.
 **
 ** There are no dependencies on CVC4 (except namespace).
 **/

#pragma once

#include <set>
#include <string>
#include <vector>

namespace CVC4 {

class DidYouMean {
 public:
  typedef std::set<std::string> Words;

  DidYouMean() {}
  ~DidYouMean() {}

  DidYouMean(Words words) : d_words(words) {}

  void addWord(std::string word) { d_words.insert(word); }

  std::vector<std::string> getMatch(std::string input);

  /**
   * This is provided to make it easier to ensure consistency of
   * output. Returned string is empty if there are no matches.
   */
  std::string getMatchAsString(std::string input, int prefixNewLines = 2,
                               int suffixNewLines = 0);

 private:
  int editDistance(const std::string& a, const std::string& b);
  Words d_words;
};

} /*CVC4 namespace*/
