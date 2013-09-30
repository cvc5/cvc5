% Status: Unsatisfiable

%--------------------------------------------------------------------------

cnf(query_1,axiom, p( A, d ) | b ).

cnf(query_1,axiom, b | c ).

cnf(query_1,axiom, ~p(A, d) | ~ 'c' ).

cnf(query_1,negated_conjecture, ~ b ).

%--------------------------------------------------------------------------
