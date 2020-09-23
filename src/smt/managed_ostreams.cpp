/*********************                                                        */
/*! \file managed_ostreams.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrappers to handle memory management of ostreams.
 **
 ** This file contains wrappers to handle special cases of managing memory
 ** related to ostreams.
 **/

#include "smt/managed_ostreams.h"

#include <ostream>

#include "base/check.h"
#include "options/open_ostream.h"
#include "options/smt_options.h"
#include "smt/update_ostream.h"

namespace CVC4 {

ManagedOstream::ManagedOstream() : d_managed(NULL) {}

ManagedOstream::~ManagedOstream() {
  manage(NULL);
  Assert(d_managed == NULL);
}

void ManagedOstream::set(const std::string& filename) {
  std::pair<bool, std::ostream*> pair = open(filename);
  initialize(pair.second);
  manage(pair.first ? pair.second : NULL);
}

std::pair<bool, std::ostream*> ManagedOstream::open(const std::string& filename)
    const {
  OstreamOpener opener(getName());
  addSpecialCases(&opener);
  return opener.open(filename);
}

void ManagedOstream::manage(std::ostream* new_managed_value) {
  if(d_managed == new_managed_value){
    // This is a no-op.
  } else {
    Assert(d_managed != new_managed_value);
    std::ostream* old_managed_value = d_managed;
    d_managed = new_managed_value;
    if(old_managed_value != NULL){
      delete old_managed_value;
    }
  }
}

ManagedDumpOStream::~ManagedDumpOStream() {
  if(Dump.getStreamPointer() == getManagedOstream()) {
    Dump.setStream(&null_os);
  }
}

std::string ManagedDumpOStream::defaultSource() const{
  return options::dumpToFileName();
}


void ManagedDumpOStream::initialize(std::ostream* outStream) {
#ifdef CVC4_DUMPING
  DumpOstreamUpdate dumpGetStream;
  dumpGetStream.apply(outStream);
#else /* CVC4_DUMPING */
  throw OptionException(
      "The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

void ManagedDumpOStream::addSpecialCases(OstreamOpener* opener) const {
  opener->addSpecialCase("-", &DumpOutC::dump_cout);
}

ManagedRegularOutputChannel::~ManagedRegularOutputChannel() {
  // Set all ostream that may still be using the old value of this channel
  // to null_os. Consult RegularOutputChannelListener for the list of
  // channels.
  if(options::err() == getManagedOstream()){
    options::err.set(&null_os);
  }
}

std::string ManagedRegularOutputChannel::defaultSource() const {
  return options::regularChannelName();
}

void ManagedRegularOutputChannel::initialize(std::ostream* outStream) {
  OptionsErrOstreamUpdate optionsErrOstreamUpdate;
  optionsErrOstreamUpdate.apply(outStream);
}

void ManagedRegularOutputChannel::addSpecialCases(OstreamOpener* opener)
    const {
  opener->addSpecialCase("stdout", &std::cout);
  opener->addSpecialCase("stderr", &std::cerr);
}

ManagedDiagnosticOutputChannel::~ManagedDiagnosticOutputChannel() {
  // Set all ostreams that may still be using the old value of this channel
  // to null_os. Consult DiagnosticOutputChannelListener for the list of
  // channels.
  if(options::err() == getManagedOstream()){
    options::err.set(&null_os);
  }

  if(Debug.getStreamPointer() == getManagedOstream()) {
    Debug.setStream(&null_os);
  }
  if(Warning.getStreamPointer() == getManagedOstream()){
    Warning.setStream(&null_os);
  }
  if(Message.getStreamPointer() == getManagedOstream()){
    Message.setStream(&null_os);
  }
  if(Notice.getStreamPointer() == getManagedOstream()){
    Notice.setStream(&null_os);
  }
  if(Chat.getStreamPointer() == getManagedOstream()){
    Chat.setStream(&null_os);
  }
  if(Trace.getStreamPointer() == getManagedOstream()){
    Trace.setStream(&null_os);
  }
}


std::string ManagedDiagnosticOutputChannel::defaultSource() const {
  return options::diagnosticChannelName();
}
void ManagedDiagnosticOutputChannel::initialize(std::ostream* outStream) {
  DebugOstreamUpdate debugOstreamUpdate;
  debugOstreamUpdate.apply(outStream);
  WarningOstreamUpdate warningOstreamUpdate;
  warningOstreamUpdate.apply(outStream);
  MessageOstreamUpdate messageOstreamUpdate;
  messageOstreamUpdate.apply(outStream);
  NoticeOstreamUpdate noticeOstreamUpdate;
  noticeOstreamUpdate.apply(outStream);
  ChatOstreamUpdate chatOstreamUpdate;
  chatOstreamUpdate.apply(outStream);
  TraceOstreamUpdate traceOstreamUpdate;
  traceOstreamUpdate.apply(outStream);
  OptionsErrOstreamUpdate optionsErrOstreamUpdate;
  optionsErrOstreamUpdate.apply(outStream);
}

void ManagedDiagnosticOutputChannel::addSpecialCases(OstreamOpener* opener)
    const {
  opener->addSpecialCase("stdout", &std::cout);
  opener->addSpecialCase("stderr", &std::cerr);
}

}/* CVC4 namespace */
