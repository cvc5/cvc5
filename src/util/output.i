%{
#include "util/output.h"
%}

%feature("valuewrapper") CVC4::null_streambuf;
%feature("valuewrapper") std::ostream;

// There are issues with SWIG's attempted wrapping of these variables when
// it tries to generate the getters and setters.  For now, just ignore them.
%ignore CVC4::null_sb;
%ignore CVC4::null_os;
%ignore CVC4::DumpOutC::dump_cout;

%ignore operator<<;
%ignore on(std::string);
%ignore isOn(std::string);
%ignore off(std::string);
%ignore printf(std::string, const char*, ...);
%ignore operator()(std::string);

%ignore CVC4::ScopedDebug::ScopedDebug(std::string);
%ignore CVC4::ScopedDebug::ScopedDebug(std::string, bool);

%ignore CVC4::ScopedTrace::ScopedTrace(std::string);
%ignore CVC4::ScopedTrace::ScopedTrace(std::string, bool);

%rename(getostream) operator std::ostream&;
%rename(getCVC4ostream) operator CVC4ostream;
%rename(get) operator();
%rename(ok) operator bool;

%include "util/output.h"
