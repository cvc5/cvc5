% Status: Satisfiable

%--------------------------------------------------------------------------

cnf(query_1,axiom, p( A, d ) | cnf ).

cnf(query_1,axiom, cnf | c ).

cnf(query_1,axiom, ~p(A, axiom) | ~ 'c' ).

cnf(query_1,axiom, axiom != d ).

cnf(query_1,negated_conjecture, ~ cnf ).

%--------------------------------------------------------------------------
