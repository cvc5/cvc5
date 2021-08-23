/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_PUBLIC_H
#define CVC5__OPTIONS__OPTIONS_PUBLIC_H

#include <iosfwd>
#include <optional>
#include <sstream>
#include <string>
#include <variant>
#include <vector>

#include "cvc5_export.h"
#include "options/options.h"

namespace cvc5::options {

bool getUfHo(const Options& opts) CVC5_EXPORT;

/**
 * Retrieve an option value by name (as given in key) from the Options object
 * opts as a string.
 */
std::string get(const Options& opts, const std::string& name) CVC5_EXPORT;

/**
 * Update the Options object opts, set the value of the option specified by key
 * to the value parsed from optionarg.
 */
void set(Options& opts,
         const std::string& name,
         const std::string& optionarg) CVC5_EXPORT;

/**
 * Get the setting for all options.
 */
std::vector<std::vector<std::string> > getAll(const Options& opts) CVC5_EXPORT;

/**
 * Get a (sorted) list of all option names that are available.
 */
std::vector<std::string> getNames() CVC5_EXPORT;

/**
 * Represents information we can provide about a particular option. It contains
 * its name and aliases, the current value and the default value as well as
 * type-specific information like its range (if it is a number) or the choices
 * (if it is a mode option).
 */
struct CVC5_EXPORT OptionInfo
{
  std::string name;
  std::vector<std::string> aliases;
  bool setByUser;

  /** No information about the options value */
  struct VoidInfo
  {
  };
  /** Default value and current value */
  template <typename T>
  struct ValueInfo
  {
    T defaultValue;
    T currentValue;
  };
  /** Default value, current value, minimum and maximum of a numeric value */
  template <typename T>
  struct NumberInfo
  {
    T defaultValue;
    T currentValue;
    std::optional<T> minimum;
    std::optional<T> maximum;
  };
  /** Default value, current value and choices of a mode option */
  struct ModeInfo
  {
    std::string defaultValue;
    std::string currentValue;
    std::vector<std::string> modes;

    template <typename T>
    ModeInfo(const std::string& def, T cur, const std::vector<std::string>& m)
        : defaultValue(def), modes(m)
    {
      std::stringstream ss;
      ss << cur;
      currentValue = ss.str();
    }
  };

  /** A variant over all possible option value information */
  std::variant<VoidInfo,
               ValueInfo<bool>,
               ValueInfo<std::string>,
               NumberInfo<int64_t>,
               NumberInfo<uint64_t>,
               NumberInfo<double>,
               ModeInfo>
      valueInfo;
};

/**
 * Retrieves information about an option specified by its name from an options
 * object. Note that `opts` is only used to retrieve the current value.
 */
OptionInfo getInfo(const Options& opts, const std::string& name) CVC5_EXPORT;

}  // namespace cvc5::options

#endif
