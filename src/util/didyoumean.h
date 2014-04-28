/*********************                                                        */
/*! \file didyoumean.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief did-you-mean style suggestions.
 **
 ** ``What do you mean? I don't understand.'' An attempt to be more
 ** helpful than that. Similar to one in git.
 **
 ** There are no dependencies on CVC4 (except namespace).
 **/

#pragma once

#include <vector>
#include <set>
#include <string>

namespace CVC4 {

class DidYouMean {
  typedef std::set<std::string> Words;
  Words d_words;

public:
  DidYouMean() {}
  ~DidYouMean() {}

  DidYouMean(Words words) : d_words(words) {}
  
  void addWord(std::string word) {
    d_words.insert(word);
  }
  
  std::vector<std::string> getMatch(std::string input);

  /**
   * This is provided to make it easier to ensure consistency of
   * output. Returned string is empty if there are no matches.
   */
  std::string getMatchAsString(std::string input, int prefixNewLines = 2, int suffixNewLines = 0);
private:
  int editDistance(const std::string& a, const std::string& b);
};

}/*CVC4 namespace*/
