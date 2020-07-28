/*********************                                                        */
/*! \file managed_ostreams.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrappers to handle memory management of ostreams.
 **
 ** This file contains wrappers to handle special cases of managing memory
 ** related to ostreams.
 **/

#include "cvc4_private.h"

#ifndef CVC4__MANAGED_OSTREAMS_H
#define CVC4__MANAGED_OSTREAMS_H

#include <ostream>

#include "options/open_ostream.h"
#include "smt/update_ostream.h"

namespace CVC4 {

/** This abstracts the management of ostream memory and initialization. */
class ManagedOstream {
 public:
  /** Initially getManagedOstream() == NULL. */
  ManagedOstream();
  virtual ~ManagedOstream();

  /** Returns the pointer to the managed ostream. */
  std::ostream* getManagedOstream() const { return d_managed; }

  /** Returns the name of the ostream geing managed. */
  virtual const char* getName() const = 0;

  /**
   * Set opens a file with filename, initializes the stream.
   * If the opened ostream is marked as managed, this calls manage(stream).
   * If the opened ostream is not marked as managed, this calls manage(NULL).
   */
  void set(const std::string& filename);

  /** If this is associated with an option, return the string value. */
  virtual std::string defaultSource() const { return ""; }

 protected:

  /**
   * Opens an ostream using OstreamOpener with the name getName() with the
   * special cases added by addSpecialCases().
   */
  std::pair<bool, std::ostream*> open(const std::string& filename) const;

  /**
   * Updates the value of managed pointer. Whenever this changes,
   * beforeRelease() is called on the old value.
   */
  void manage(std::ostream* new_managed_value);

  /** Initializes an output stream. Not necessarily managed. */
  virtual void initialize(std::ostream* outStream) {}

  /** Adds special cases to an ostreamopener. */
  virtual void addSpecialCases(OstreamOpener* opener) const {}

 private:
  std::ostream* d_managed;
}; /* class ManagedOstream */

/**
 * This controls the memory associated with --dump-to.
 * This is is assumed to recieve a set whenever diagnosticChannelName
 * is updated.
 */
class ManagedDumpOStream : public ManagedOstream {
 public:
  ManagedDumpOStream(){}
  ~ManagedDumpOStream();

  const char* getName() const override { return "dump-to"; }
  std::string defaultSource() const override;

 protected:
  /** Initializes an output stream. Not necessarily managed. */
  void initialize(std::ostream* outStream) override;

  /** Adds special cases to an ostreamopener. */
  void addSpecialCases(OstreamOpener* opener) const override;
};/* class ManagedDumpOStream */

/**
 * When d_managedRegularChannel is non-null, it owns the memory allocated
 * with the regular-output-channel. This is set when
 * options::regularChannelName is set.
 */
class ManagedRegularOutputChannel : public ManagedOstream {
 public:
  ManagedRegularOutputChannel(){}

  /** Assumes Options are in scope. */
  ~ManagedRegularOutputChannel();

  const char* getName() const override { return "regular-output-channel"; }
  std::string defaultSource() const override;

 protected:
  /** Initializes an output stream. Not necessarily managed. */
  void initialize(std::ostream* outStream) override;

  /** Adds special cases to an ostreamopener. */
  void addSpecialCases(OstreamOpener* opener) const override;
};/* class ManagedRegularOutputChannel */


/**
 * This controls the memory associated with diagnostic-output-channel.
 * This is is assumed to recieve a set whenever options::diagnosticChannelName
 * is updated.
 */
class ManagedDiagnosticOutputChannel : public ManagedOstream {
 public:
  ManagedDiagnosticOutputChannel(){}

  /** Assumes Options are in scope. */
  ~ManagedDiagnosticOutputChannel();

  const char* getName() const override { return "diagnostic-output-channel"; }
  std::string defaultSource() const override;

 protected:
  /** Initializes an output stream. Not necessarily managed. */
  void initialize(std::ostream* outStream) override;

  /** Adds special cases to an ostreamopener. */
  void addSpecialCases(OstreamOpener* opener) const override;
};/* class ManagedRegularOutputChannel */

}/* CVC4 namespace */

#endif /* CVC4__MANAGED_OSTREAMS_H */
