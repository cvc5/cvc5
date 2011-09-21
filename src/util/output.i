%{
#include "util/output.h"
%}

%feature("valuewrapper") CVC4::null_streambuf;
%feature("valuewrapper") std::ostream;

// There are issues with SWIG's attempted wrapping of these variables when
// it tries to generate the getters and setters.  For now, just ignore them.
%ignore CVC4::null_sb;
%ignore CVC4::null_os;
%ignore CVC4::DumpC::dump_cout;

%include "util/output.h"
