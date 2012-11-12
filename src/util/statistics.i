%{
#include "util/statistics.h"
%}

%rename(assign) CVC4::Statistics::operator=(const StatisticsBase&);
%rename(assign) CVC4::Statistics::operator=(const Statistics& stats);

%include "util/statistics.h"
