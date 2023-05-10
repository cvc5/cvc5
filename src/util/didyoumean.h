/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Kshitij Bansal, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include <cvc5/cvc5_export.h>

#include <string>
#include <vector>

namespace cvc5::internal {

class CVC5_EXPORT DidYouMean {
 public:
  void addWord(const std::string& word) { d_words.emplace_back(word); }
  void addWords(const std::vector<std::string>& words)
  {
    d_words.insert(d_words.end(), words.begin(), words.end());
  }

  std::vector<std::string> getMatch(const std::string& input);

  /**
   * This is provided to make it easier to ensure consistency of
   * output. Returned string is empty if there are no matches.
   */
  std::string getMatchAsString(const std::string& input);

 private:
  std::vector<std::string> d_words;
};

}  // namespace cvc5::internal
