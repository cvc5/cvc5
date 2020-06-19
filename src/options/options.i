%{
#include "options/options.h"
%}

%ignore CVC4::Options::registerAndNotify(ListenerCollection& collection, Listener* listener, bool notify);
%ignore CVC4::Options::registerBeforeSearchListener(Listener* listener);
%ignore CVC4::Options::registerTlimitListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerTlimitPerListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerRlimitListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerRlimitPerListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetDefaultExprDepthListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetDefaultExprDagListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetPrintExprTypesListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetDumpModeListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetPrintSuccessListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerDumpToFileNameListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetRegularOutputChannelListener(Listener* listener, bool notifyIfSet);
%ignore CVC4::Options::registerSetDiagnosticOutputChannelListener(Listener* listener, bool notifyIfSet);

%apply char** STRING_ARRAY { char* argv[] }
%include "options/options.h"
%clear char* argv[];
