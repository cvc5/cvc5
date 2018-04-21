/*********************                                                        */
/*! \file update_ostream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UPDATE_OSTREAM_H
#define __CVC4__UPDATE_OSTREAM_H

#include <ostream>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "options/language.h"
#include "options/set_language.h"
#include "options/base_options.h"
#include "smt/dump.h"

namespace CVC4 {

class ChannelSettings {
 public:
  ChannelSettings(std::ostream& out)
      : d_dagSetting(expr::ExprDag::getDag(out)),
        d_exprDepthSetting(expr::ExprSetDepth::getDepth(out)),
        d_printtypesSetting(expr::ExprPrintTypes::getPrintTypes(out)),
        d_languageSetting(language::SetLanguage::getLanguage(out))
  {}

  void apply(std::ostream& out) {
    out << expr::ExprDag(d_dagSetting);
    out << expr::ExprSetDepth(d_exprDepthSetting);
    out << expr::ExprPrintTypes(d_printtypesSetting);
    out << language::SetLanguage(d_languageSetting);
  }

 private:
  const int d_dagSetting;
  const size_t d_exprDepthSetting;
  const bool d_printtypesSetting;
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
  void set(std::ostream* setTo) override { return options::err.set(setTo); }
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
  std::ostream& get() override { return Message.getStream(); }
  void set(std::ostream* setTo) override { Message.setStream(setTo); }
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

}/* CVC4 namespace */

#endif /* __CVC4__UPDATE_OSTREAM_H */
