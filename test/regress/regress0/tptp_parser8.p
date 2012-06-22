% EXPECT: unknown (INCOMPLETE)
% EXIT: 0

%--------------------------------------------------------------------------
include('tptp_parser7.p').

cnf(query_1,axiom, include('A') | b ).

cnf(query_1,negated_conjecture, ~ b ).

%--------------------------------------------------------------------------
