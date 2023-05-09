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

#include "util/didyoumean.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <sstream>
#include <string>
#include <vector>

namespace cvc5::internal {

namespace {

uint64_t editDistance(const std::string& a, const std::string& b) {
  // input string: a
  // desired string: b

  constexpr uint64_t swapCost = 0;
  constexpr uint64_t substituteCost = 2;
  constexpr uint64_t addCost = 1;
  constexpr uint64_t deleteCost = 2;
  constexpr uint64_t switchCaseCost = 0;

  uint64_t len1 = a.size();
  uint64_t len2 = b.size();

  std::array<std::vector<uint64_t>, 3> C;
  for (auto& c: C)
  {
    c.resize(len2 + 1);
  }
  //  int C[3][len2+1];             // cost

  for (uint64_t j = 0; j <= len2; ++j)
  {
    C[0][j] = j * addCost;
  }

  for (uint64_t i = 1; i <= len1; ++i)
  {
    uint64_t cur = i % 3;
    uint64_t prv = (i + 2) % 3;
    uint64_t pr2 = (i + 1) % 3;

    C[cur][0] = i * deleteCost;

    for (uint64_t j = 1; j <= len2; ++j)
    {
      C[cur][j] = 100000000;  // INF

      if (a[i - 1] == b[j - 1]) {
        // match
        C[cur][j] = std::min(C[cur][j], C[prv][j - 1]);
      } else if (tolower(a[i - 1]) == tolower(b[j - 1])) {
        // switch case
        C[cur][j] = std::min(C[cur][j], C[prv][j - 1] + switchCaseCost);
      } else {
        // substitute
        C[cur][j] = std::min(C[cur][j], C[prv][j - 1] + substituteCost);
      }

      // swap
      if (i >= 2 && j >= 2 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1]) {
        C[cur][j] = std::min(C[cur][j], C[pr2][j - 2] + swapCost);
      }

      // add
      C[cur][j] = std::min(C[cur][j], C[cur][j - 1] + addCost);

      // delete
      C[cur][j] = std::min(C[cur][j], C[prv][j] + deleteCost);
    }
  }
  return C[len1 % 3][len2];
}

}

std::vector<std::string> DidYouMean::getMatch(const std::string& input)
{
  {
    std::sort(d_words.begin(), d_words.end());
    auto it = std::unique(d_words.begin(), d_words.end());
    d_words.erase(it, d_words.end());
  }

  /** Magic numbers */
  constexpr uint64_t similarityThreshold = 10;
  constexpr uint64_t numMatchesThreshold = 10;

  std::vector<std::pair<uint64_t,std::string>> scores;
  std::vector<std::string> ret;
  for (const auto& s: d_words) {
    if (s == input) {
      // if input matches AS-IS just return that
      ret.emplace_back(s);
      return ret;
    }
    uint64_t score = 0;
    if (s.compare(0, input.size(), input) != 0) {
      score = editDistance(input, s) + 1;
    }
    scores.emplace_back(std::make_pair(score, s));
  }
  std::sort(scores.begin(), scores.end());
  const uint64_t min_score = scores.begin()->first;
  for (const auto& score: scores) {
    // from here on, matches are not similar enough
    if (score.first > similarityThreshold) break;
    // from here on, matches are way worse than the best one
    if (score.first > min_score + 4) break;
    // we already have enough matches
    if (ret.size() >= numMatchesThreshold) break;
    ret.push_back(score.second);
  }
  return ret;
}

std::string DidYouMean::getMatchAsString(const std::string& input)
{
  std::vector<std::string> matches = getMatch(input);
  std::ostringstream oss;
  if (matches.size() > 0) {
    oss << std::endl << std::endl;
    if (matches.size() == 1) {
      oss << "Did you mean this?";
    } else {
      oss << "Did you mean any of these?";
    }
    for (size_t i = 0; i < matches.size(); ++i)
    {
      oss << "\n        " << matches[i];
    }
  }
  return oss.str();
}

}  // namespace cvc5::internal
