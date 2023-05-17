/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "base/check.h"
#include "base/output.h"
#include "options/io_utils.h"
#include "options/options.h"
#include "options/options_handler.h"
#include "options/options_listener.h"
#include "options/options_public.h"
#include "options/uf_options.h"

// clang-format off
${headers_module}$
${options_includes}$
// clang-format on

#include <cstring>
#include <iostream>
#include <limits>

namespace {
  // clang-format off
  ${option_enum_and_table}$
  // clang-format on
}

namespace cvc5::internal::options
{
  // Contains the default option handlers (i.e. parsers)
  namespace handlers {

  /**
   * Utility function for handling numeric options. Takes care of checking for
   * unsignedness, parsing and handling parsing exceptions. Expects `conv` to be
   * a conversion function like `std::stod`, accepting a `std::string` and a
   * `size_t*`. The argument `type` is only used to generate proper error
   * messages and should be the string representation of `T`. If `T` is
   * unsigned, checks that `optionarg` contains no minus. Then `conv` is called
   * and the error conditions are handled: `conv` may throw an exception or
   * `pos` may be smaller than the size of `optionarg`, indicating that not the
   * entirety of `optionarg` was parsed.
   */
  template <typename T, typename FF>
  T parseNumber(const std::string& flag,
                const std::string& optionarg,
                FF&& conv,
                const std::string& type)
  {
    if (!std::numeric_limits<T>::is_signed
        && (optionarg.find('-') != std::string::npos))
    {
      std::stringstream ss;
      ss << "Argument '" << optionarg << "' for " << type << " option " << flag
         << " is negative";
      throw OptionException(ss.str());
    }
    size_t pos = 0;
    T res;
    try
    {
      res = conv(optionarg, &pos);
    }
    catch (const std::exception& e)
    {
      std::stringstream ss;
      ss << "Argument '" << optionarg << "' for " << type << " option " << flag
         << " did not parse as " << type;
      throw OptionException(ss.str());
    }
    if (pos < optionarg.size())
    {
      std::stringstream ss;
      ss << "Argument '" << optionarg << "' for " << type << " option " << flag
         << " did parse only partially as " << type << ", leaving '"
         << optionarg.substr(pos) << "'";
      throw OptionException(ss.str());
    }
    return res;
  }

  /** Default handler that triggers a compiler error */
  template <typename T>
  T handleOption(const std::string& flag, const std::string& optionarg)
  {
    T::unsupported_handleOption_specialization;
    return *static_cast<T*>(nullptr);
  }

  /** Handle a string option by returning it as is. */
  template <>
  std::string handleOption<std::string>(const std::string& flag,
                                        const std::string& optionarg)
  {
    return optionarg;
  }
  /** Handle a bool option, recognizing "true" or "false". */
  template <>
  bool handleOption<bool>(const std::string& flag, const std::string& optionarg)
  {
    if (optionarg == "true")
    {
      return true;
    }
    if (optionarg == "false")
    {
      return false;
    }
    throw OptionException("Argument '" + optionarg + "' for bool option " + flag
                          + " is not a bool constant");
  }

  /** Handle a double option, using `parseNumber` with `std::stod`. */
  template <>
  double handleOption<double>(const std::string& flag,
                              const std::string& optionarg)
  {
    return parseNumber<double>(
        flag,
        optionarg,
        [](const auto& s, auto p) { return std::stod(s, p); },
        "double");
  }

  /** Handle a int64_t option, using `parseNumber` with `std::stoll`. */
  template <>
  int64_t handleOption<int64_t>(const std::string& flag,
                                const std::string& optionarg)
  {
    return parseNumber<int64_t>(
        flag,
        optionarg,
        [](const auto& s, auto p) { return std::stoll(s, p); },
        "int64_t");
  }

  /** Handle a uint64_t option, using `parseNumber` with `std::stoull`. */
  template <>
  uint64_t handleOption<uint64_t>(const std::string& flag,
                                  const std::string& optionarg)
  {
    return parseNumber<uint64_t>(
        flag,
        optionarg,
        [](const auto& s, auto p) { return std::stoull(s, p); },
        "uint64_t");
  }

  /** Handle a ManagedIn option. */
  template <>
  ManagedIn handleOption<ManagedIn>(const std::string& flag,
                                    const std::string& optionarg)
  {
    ManagedIn res;
    res.open(optionarg);
    return res;
  }

  /** Handle a ManagedErr option. */
  template <>
  ManagedErr handleOption<ManagedErr>(const std::string& flag,
                                      const std::string& optionarg)
  {
    ManagedErr res;
    res.open(optionarg);
    return res;
  }

  /** Handle a ManagedOut option. */
  template <>
  ManagedOut handleOption<ManagedOut>(const std::string& flag,
                                      const std::string& optionarg)
  {
    ManagedOut res;
    res.open(optionarg);
    return res;
  }
  }

  std::vector<std::string> getNames()
  {
    return {
        // clang-format off
    ${getnames_impl}$
        // clang-format on
    };
  }

  std::string get(const Options& options, const std::string& name)
  {
    Trace("options") << "Options::getOption(" << name << ")" << std::endl;
    // clang-format off
    ${get_impl}$
    // clang-format on
    throw OptionException("Unrecognized option key or setting: " + name);
  }

  void set(
      Options & opts, const std::string& name, const std::string& optionarg)
  {
    Trace("options") << "set option " << name << " = " << optionarg
                     << std::endl;
    // clang-format off
    ${set_impl}$
    // clang-format on
  }

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

OptionInfo getInfo(const Options& opts, const std::string& name)
{
  // clang-format off
  ${getinfo_impl}$
  // clang-format on
  return OptionInfo{"", {}, false, OptionInfo::VoidInfo{}};
}

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}  // namespace cvc5::internal::options
