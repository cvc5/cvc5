%{
#include "smt/command.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

#endif /* SWIGJAVA */
%}

%ignore CVC4::operator<<(std::ostream&, const Command&) throw();
%ignore CVC4::operator<<(std::ostream&, const Command*) throw();
%ignore CVC4::operator<<(std::ostream&, const CommandStatus&) throw();
%ignore CVC4::operator<<(std::ostream&, const CommandStatus*) throw();
%ignore CVC4::operator<<(std::ostream&, BenchmarkStatus status) throw();
%ignore CVC4::operator<<(std::ostream&, CommandPrintSuccess) throw();

%ignore CVC4::GetProofCommand;
%ignore CVC4::CommandPrintSuccess::Scope;

#ifdef SWIGJAVA

// Instead of CommandSequence::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::CommandSequence::begin();
%ignore CVC4::CommandSequence::end();
%ignore CVC4::CommandSequence::begin() const;
%ignore CVC4::CommandSequence::end() const;
%extend CVC4::CommandSequence {
  CVC4::JavaIteratorAdapter<CVC4::CommandSequence> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::CommandSequence>(*$self);
  }
}

// CommandSequence is "iterable" on the Java side
%typemap(javainterfaces) CVC4::CommandSequence "java.lang.Iterable<edu.nyu.acsys.CVC4.Command>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::CommandSequence> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::CommandSequence> "java.util.Iterator<edu.nyu.acsys.CVC4.Command>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::CommandSequence> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public edu.nyu.acsys.CVC4.Command next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"
// getNext() just allows C++ iterator access from Java-side next(), make it private
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::CommandSequence>::getNext() "private";

// map the types appropriately
%typemap(jni) CVC4::CommandSequence::const_iterator::value_type "jobject";
%typemap(jtype) CVC4::CommandSequence::const_iterator::value_type "edu.nyu.acsys.CVC4.Command";
%typemap(jstype) CVC4::CommandSequence::const_iterator::value_type "edu.nyu.acsys.CVC4.Command";
%typemap(javaout) CVC4::CommandSequence::const_iterator::value_type { return $jnicall; }

#endif /* SWIGJAVA */

%include "smt/command.h"

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"

%template(JavaIteratorAdapter_CommandSequence) CVC4::JavaIteratorAdapter<CVC4::CommandSequence>;

#endif /* SWIGJAVA */
