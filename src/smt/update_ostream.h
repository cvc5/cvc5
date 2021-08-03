/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__UPDATE_OSTREAM_H
#define CVC5__UPDATE_OSTREAM_H

#include <ostream>

#include "base/check.h"
#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/set_language.h"
#include "smt/dump.h"

namespace cvc5 {

class ChannelSettings {
 public:
  ChannelSettings(std::ostream& out)
      : d_dagSetting(expr::ExprDag::getDag(out)),
        d_exprDepthSetting(expr::ExprSetDepth::getDepth(out)),
        d_languageSetting(language::SetLanguage::getLanguage(out))
  {}

  void apply(std::ostream& out) {
    out << expr::ExprDag(d_dagSetting);
    out << expr::ExprSetDepth(d_exprDepthSetting);
    out << language::SetLanguage(d_languageSetting);
  }

 private:
  const int d_dagSetting;
  const size_t d_exprDepthSetting;
  const OutputLanguage d_languageSetting;
}; /* class ChannelSettings */

class OstreamUpdate {
public:
  virtual ~OstreamUpdate(){}

  virtual std::ostream& get() = 0;
  virtual void set(std::ostream* setTo) = 0;

  void apply(std::ostream* setTo) {
    PrettyCheckArgument(setTo != NULL, setTo);

    ChannelSettings initialSettings(get());
    set(setTo);
    initialSettings.apply(get());
  }
}; /* class OstreamUpdate */

class OptionsErrOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return *(options::err()); }
  void set(std::ostream* setTo) override { Options::current().base.err = setTo; }
};  /* class OptionsErrOstreamUpdate */

class DumpOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return Dump.getStream(); }
  void set(std::ostream* setTo) override { Dump.setStream(setTo); }
};  /* class DumpOstreamUpdate */

class DebugOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return Debug.getStream(); }
  void set(std::ostream* setTo) override { Debug.setStream(setTo); }
};  /* class DebugOstreamUpdate */

class WarningOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return Warning.getStream(); }
  void set(std::ostream* setTo) override { Warning.setStream(setTo); }
};  /* class WarningOstreamUpdate */

class MessageOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return CVC5Message.getStream(); }
  void set(std::ostream* setTo) override { CVC5Message.setStream(setTo); }
};  /* class MessageOstreamUpdate */

class NoticeOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return Notice.getStream(); }
  void set(std::ostream* setTo) override { Notice.setStream(setTo); }
};  /* class NoticeOstreamUpdate */

class ChatOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return Chat.getStream(); }
  void set(std::ostream* setTo) override { Chat.setStream(setTo); }
};  /* class ChatOstreamUpdate */

class TraceOstreamUpdate : public OstreamUpdate {
 public:
  std::ostream& get() override { return Trace.getStream(); }
  void set(std::ostream* setTo) override { Trace.setStream(setTo); }
};  /* class TraceOstreamUpdate */

}  // namespace cvc5

#endif /* CVC5__UPDATE_OSTREAM_H */
