%{
#include "util/tuple.h"
%}

%rename(equals) CVC4::TupleSelect::operator==(const TupleSelect&) const;
%ignore CVC4::TupleSelect::operator!=(const TupleSelect&) const;

%rename(equals) CVC4::TupleUpdate::operator==(const TupleUpdate&) const;
%ignore CVC4::TupleUpdate::operator!=(const TupleUpdate&) const;

%include "util/tuple.h"
