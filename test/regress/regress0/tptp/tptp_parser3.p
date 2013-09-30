% Status: Unsatisfiable

%--------------------------------------------------------------------------

cnf(query_1,axiom, p( a, d ) | b ).

cnf(query_1,axiom, b | c ).

cnf(query_1,axiom, ~p(a, d) | ~ 'c' ).

cnf(query_1,negated_conjecture, ~ b ).

%--------------------------------------------------------------------------
