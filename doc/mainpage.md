/**
\mainpage Getting started with the CVC4 API

The main classes of the CVC4 API are:
- CVC4::Expr - an expression (a formula, term, variable, constant, etc.)
- CVC4::Type - a type (every Expr has a Type)
- CVC4::ExprManager - a factory class for Exprs and Types (create one of these for your application)
- CVC4::SmtEngine - the SMT interface, permits making assertions and checking satisfiability (create one of these for your application)

There are numerous examples of the use of the C++ API in the examples/api directory of the CVC4 source distribution.  There is also a discussion on our CVC4 Wiki at
http://cvc4.cs.nyu.edu/wiki/Tutorials#C.2B.2B_API

Using the CVC4 API from Java

While these API documentation resources explicitly refer to the C++ interface, the Java interface is generated automatically from the C++ sources by SWIG, and thus the interface is almost line-by-line identical in Java.  It is possible, then, to use these C++ resources to help with the Java API.  There are three main ways in which the Java API differs from the C++ API.  First, the CVC4 API makes moderate use of C++ operator overloading, which is not possible in Java.  We have provided standard renamings for the Java methods associated to these C++ overloaded operators---for instance, "plus" replaces operator+, "equals" replaces operator==, etc.

Secondly, C++ iterators are replaced by Java iterators.  Instead of begin() and end() on classes like CVC4::Expr, you'll notice in the Java interface that there is an iterator() method that returns a java.util.Iterator<Expr>.  This allows Java developers to more naturally work with our (ultimately C++) objects through a more Java-like interface.

Third, I/O streams are wrapped so that some functions requiring C++ input and output streams will accept Java InputStreams and OutputStreams.

Our intent is to make the C++ API as useful and functional for Java developers as possible, while still retaining the flexibility of our original C++ design.  If we can make your life as a Java user of our libraries easier, please let us know by requesting an enhancement or reporting a bug at our bug-tracking service, https://github.com/CVC4/CVC4/issues.

For examples of Java programs using the CVC4 API, look in the directory examples/api/java in the CVC4 source distribution.

Thank you for your interest in CVC4!

The CVC4 Development team

\page authors AUTHORS
\verbinclude AUTHORS
\page copying COPYING
\verbinclude COPYING
\page install INSTALL
\verbinclude INSTALL
\page news NEWS
\verbinclude NEWS
\page release-notes RELEASE-NOTES
\verbinclude RELEASE-NOTES
\page readme README
\verbinclude README
\page thanks THANKS
\verbinclude THANKS
*/
