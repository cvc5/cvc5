%--------------------------------------------------------------------------
% File     : SYN075-1 : TPTP v5.5.0. Released v1.0.0.
% Domain   : Syntactic
% Problem  : Pelletier Problem 52
% Version  : Especial.
% English  :

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 52 [Pel86]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.5.0, 0.20 v5.3.0, 0.22 v5.2.0, 0.12 v5.1.0, 0.06 v5.0.0, 0.07 v4.1.0, 0.08 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.00 v3.3.0, 0.14 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.5.0, 0.08 v2.4.0, 0.11 v2.2.1, 0.11 v2.2.0, 0.22 v2.1.0, 0.33 v2.0.0
% Syntax   : Number of clauses     :   10 (   4 non-Horn;   0 unit;   8 RR)
%            Number of atoms       :   31 (  17 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   2 constant; 0-2 arity)
%            Number of variables   :   23 (   2 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,axiom,
    ( ~ big_f(X,Y)
    | X = a )).

cnf(clause_2,axiom,
    ( ~ big_f(X,Y)
    | Y = b )).

cnf(clause_3,axiom,
    ( X != a
    | Y != b
    | big_f(X,Y) )).

cnf(clause_4,negated_conjecture,
    ( ~ big_f(Y,f(X))
    | Y != g(X)
    | f(X) = X )).

cnf(clause_5,negated_conjecture,
    ( ~ big_f(Y,f(X))
    | Y = g(X)
    | big_f(h(X,Z),f(X))
    | ~ big_f(h(X,Z),f(X)) )).

cnf(clause_6,negated_conjecture,
    ( Y != g(X)
    | big_f(Y,f(X))
    | f(X) = X )).

cnf(clause_7,negated_conjecture,
    ( Y != g(X)
    | big_f(Y,f(X))
    | big_f(h(X,Z),f(X))
    | h(X,Z) = Z )).

cnf(clause_8,negated_conjecture,
    ( Y != g(X)
    | big_f(Y,f(X))
    | h(X,Z) != Z
    | ~ big_f(h(X,Z),f(X)) )).

cnf(clause_9,negated_conjecture,
    ( f(X) != X
    | big_f(h(X,Z),f(X))
    | h(X,Z) = Z )).

cnf(clause_10,negated_conjecture,
    ( f(X) != X
    | h(X,Z) != Z
    | ~ big_f(h(X,Z),f(X)) )).

%--------------------------------------------------------------------------
