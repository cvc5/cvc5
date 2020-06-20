%{
#include "util/statistics.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"

#endif /* SWIGJAVA */
%}

%include "stdint.i"

%rename(assign) CVC4::Statistics::operator=(const StatisticsBase&);
%rename(assign) CVC4::Statistics::operator=(const Statistics& stats);

#ifdef SWIGJAVA

// Instead of StatisticsBase::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::StatisticsBase::begin();
%ignore CVC4::StatisticsBase::end();
%ignore CVC4::StatisticsBase::begin() const;
%ignore CVC4::StatisticsBase::end() const;
%extend CVC4::StatisticsBase {
  CVC4::JavaIteratorAdapter<CVC4::StatisticsBase,
                            std::pair<std::string, CVC4::SExpr> >
  iterator()
  {
    return CVC4::JavaIteratorAdapter<CVC4::StatisticsBase,
                                     std::pair<std::string, CVC4::SExpr> >(
        *$self);
  }
}

// StatisticsBase is "iterable" on the Java side
%typemap(javainterfaces) CVC4::StatisticsBase "java.lang.Iterable<Statistic>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase, std::pair<std::string, CVC4::SExpr> > "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase, std::pair<std::string, CVC4::SExpr> > "java.util.Iterator<Statistic>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase, std::pair<std::string, CVC4::SExpr> > "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public Statistic next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"
// getNext() just allows C++ iterator access from Java-side next(), make it private
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::StatisticsBase, std::pair<std::string, CVC4::SExpr> >::getNext() "private";

#endif /* SWIGJAVA */

%include "util/statistics.h"

#ifdef SWIGJAVA

%include <std_pair.i>
%include <std_string.i>

%include "util/sexpr.h"

%template(Statistic) std::pair<std::string, CVC4::SExpr>;

%feature("valuewrapper") CVC4::JavaIteratorAdapter<CVC4::StatisticsBase, std::pair<std::string, CVC4::SExpr> >;
%template(JavaIteratorAdapter_StatisticsBase) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase, std::pair<std::string, CVC4::SExpr> >;

#endif /* SWIGJAVA */
