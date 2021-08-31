/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Andrew Reynolds
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

#include "options/options_public.h"


#include "base/check.h"
#include "base/output.h"
#include "options/options_handler.h"
#include "options/options_listener.h"
#include "options/options.h"
#include "options/uf_options.h"
${headers_module}$
${headers_handler}$

#include <cstring>
#include <iostream>
#include <limits>

namespace cvc5::options {

bool getUfHo(const Options& opts) { return opts.uf.ufHo; }

/** Set a given Options* as "current" just for a particular scope. */
class OptionsGuard {
  Options** d_field;
  Options* d_old;
public:
  OptionsGuard(Options** field, Options* opts) :
    d_field(field),
    d_old(*field) {
    *field = opts;
  }
  ~OptionsGuard() {
    *d_field = d_old;
  }
};/* class OptionsGuard */


/**
 * This is a default handler for options of built-in C++ type.  This
 * template is really just a helper for the handleOption() template,
 * below.  Variants of this template handle numeric and non-numeric,
 * integral and non-integral, signed and unsigned C++ types.
 * handleOption() makes sure to instantiate the right one.
 *
 * This implements default behavior when e.g. an option is
 * unsigned but the user specifies a negative argument; etc.
 */
template <class T, bool is_numeric, bool is_integer>
struct OptionHandler {
  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg);
};/* struct OptionHandler<> */

/** Variant for integral C++ types */
template <class T>
struct OptionHandler<T, true, true> {
  static bool stringToInt(T& t, const std::string& str) {
    std::istringstream ss(str);
    ss >> t;
    char tmp;
    return !(ss.fail() || ss.get(tmp));
  }

  static bool containsMinus(const std::string& str) {
    return str.find('-') != std::string::npos;
  }

  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg) {
    try {
      T i;
      bool success = stringToInt(i, optionarg);

      if(!success){
        throw OptionException(flag + ": failed to parse "+ optionarg +
                              " as an integer of the appropriate type.");
      }

      // Depending in the platform unsigned numbers with '-' signs may parse.
      // Reject these by looking for any minus if it is not signed.
      if( (! std::numeric_limits<T>::is_signed) && containsMinus(optionarg) ) {
        // unsigned type but user gave negative argument
        throw OptionException(flag + " requires a nonnegative argument");
      } else if(i < std::numeric_limits<T>::min()) {
        // negative overflow for type
        std::stringstream ss;
        ss << flag << " requires an argument >= "
           << std::numeric_limits<T>::min();
        throw OptionException(ss.str());
      } else if(i > std::numeric_limits<T>::max()) {
        // positive overflow for type
        std::stringstream ss;
        ss << flag << " requires an argument <= "
           << std::numeric_limits<T>::max();
        throw OptionException(ss.str());
      }

      return i;

      // if(std::numeric_limits<T>::is_signed) {
      //   return T(i.getLong());
      // } else {
      //   return T(i.getUnsignedLong());
      // }
    } catch(std::invalid_argument&) {
      // user gave something other than an integer
      throw OptionException(flag + " requires an integer argument");
    }
  }
};/* struct OptionHandler<T, true, true> */

/** Variant for numeric but non-integral C++ types */
template <class T>
struct OptionHandler<T, true, false> {
  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg) {
    std::stringstream inss(optionarg);
    long double r;
    inss >> r;
    if(! inss.eof()) {
      // we didn't consume the whole string (junk at end)
      throw OptionException(flag + " requires a numeric argument");
    }

    if(! std::numeric_limits<T>::is_signed && r < 0.0) {
      // unsigned type but user gave negative value
      throw OptionException(flag + " requires a nonnegative argument");
    } else if(r < -std::numeric_limits<T>::max()) {
      // negative overflow for type
      std::stringstream ss;
      ss << flag << " requires an argument >= "
         << -std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    } else if(r > std::numeric_limits<T>::max()) {
      // positive overflow for type
      std::stringstream ss;
      ss << flag << " requires an argument <= "
         << std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    }

    return T(r);
  }
};/* struct OptionHandler<T, true, false> */

/** Variant for non-numeric C++ types */
template <class T>
struct OptionHandler<T, false, false> {
  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg) {
    T::unsupported_handleOption_call___please_write_me;
    // The above line causes a compiler error if this version of the template
    // is ever instantiated (meaning that a specialization is missing).  So
    // don't worry about the segfault in the next line, the "return" is only
    // there to keep the compiler from giving additional, distracting errors
    // and warnings.
    return *(T*)0;
  }
};/* struct OptionHandler<T, false, false> */

/** Specialization for ManagedErr */
template <>
struct OptionHandler<ManagedErr, false, false>
{
  static ManagedErr handle(const std::string& option,
                           const std::string& flag,
                           const std::string& optionarg)
  {
    ManagedErr res;
    res.open(optionarg);
    return res;
  }
};
/** Specialization for ManagedIn */
template <>
struct OptionHandler<ManagedIn, false, false>
{
  static ManagedIn handle(const std::string& option,
                          const std::string& flag,
                          const std::string& optionarg)
  {
    ManagedIn res;
    res.open(optionarg);
    return res;
  }
};
/** Specialization for ManagedOut */
template <>
struct OptionHandler<ManagedOut, false, false>
{
  static ManagedOut handle(const std::string& option,
                           const std::string& flag,
                           const std::string& optionarg)
  {
    ManagedOut res;
    res.open(optionarg);
    return res;
  }
};

/** Handle an option of type T in the default way. */
template <class T>
T handleOption(const std::string& option, const std::string& flag, const std::string& optionarg) {
  return OptionHandler<T, std::numeric_limits<T>::is_specialized, std::numeric_limits<T>::is_integer>::handle(option, flag, optionarg);
}

/** Handle an option of type std::string in the default way. */
template <>
std::string handleOption<std::string>(const std::string& option, const std::string& flag, const std::string& optionarg) {
  return optionarg;
}
template <>
bool handleOption<bool>(const std::string& option, const std::string& flag, const std::string& optionarg) {
  Assert(optionarg == "true" || optionarg == "false");
  return optionarg == "true";
}

std::string get(const Options& options, const std::string& name)
{
  Trace("options") << "Options::getOption(" << name << ")" << std::endl;
  // clang-format off
  ${getoption_handlers}$
  // clang-format on
  throw OptionException("Unrecognized option key or setting: " + name);
}

void setInternal(Options& opts, const std::string& name,
                                const std::string& optionarg)
{
  // clang-format off
${setoption_handlers}$
  // clang-format on
  }
  else
  {
    throw OptionException("Unrecognized option key or setting: " + name);
  }
  Trace("options") << "user assigned option " << name << " = " << optionarg << std::endl;
}

void set(Options& opts, const std::string& name, const std::string& optionarg)
{

  Trace("options") << "setOption(" << name << ", " << optionarg << ")"
                   << std::endl;
  // first update this object
  setInternal(opts, name, optionarg);
}

std::vector<std::vector<std::string> > getAll(const Options& opts)
{
  std::vector<std::vector<std::string>> res;
  // clang-format off
  ${options_getall}$
  // clang-format on
  return res;
}

std::vector<std::string> getNames()
{
  return {
    // clang-format off
    ${options_all_names}$
    // clang-format on
  };
}

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

OptionInfo getInfo(const Options& opts, const std::string& name)
{
  // clang-format off
  ${options_get_info}$
  // clang-format on
  return OptionInfo{name, {}, false, OptionInfo::VoidInfo{}};
}

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}  // namespace cvc5::options
