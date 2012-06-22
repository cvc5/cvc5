% EXPECT: unsat
% EXIT: 20

%--------------------------------------------------------------------------

/*
cnf(query_1,axiom,
    $false | $false /* | $false).
*/

cnf(query_1,axiom,
    $false | $false | $false).

cnf(query_1,negated_conjecture, ~
    $false | $false | $false).

%--------------------------------------------------------------------------
