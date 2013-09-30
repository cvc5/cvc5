% Status: Satisfiable

%--------------------------------------------------------------------------

cnf(query_1,axiom, p( A, d ) | b ).

cnf(query_1,axiom, b | c ).

cnf(query_1,axiom, ~p(A, axiom) ).

cnf(query_1,axiom, axiom != d ).

cnf(query_1,negated_conjecture, ~ b ).

%--------------------------------------------------------------------------
