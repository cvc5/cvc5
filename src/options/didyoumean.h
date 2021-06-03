/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Did-you-mean style suggestions.
 *
 * ``What do you mean? I don't understand.'' An attempt to be more
 * helpful than that. Similar to one in git.
 *
 * There are no dependencies on cvc5 (except namespace).
 */

#pragma once

#include <set>
#include <string>
#include <vector>

namespace cvc5 {

class DidYouMean {
 public:
  using Words = std::set<std::string>;

  DidYouMean() {}
  ~DidYouMean() {}

  void addWord(std::string word) { d_words.insert(std::move(word)); }

  std::vector<std::string> getMatch(const std::string& input);

  /**
   * This is provided to make it easier to ensure consistency of
   * output. Returned string is empty if there are no matches.
   */
  std::string getMatchAsString(const std::string& input,
                               uint64_t prefixNewLines = 2,
                               uint64_t suffixNewLines = 0);

 private:
  int editDistance(const std::string& a, const std::string& b);
  Words d_words;
};

}  // namespace cvc5
