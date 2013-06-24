%--------------------------------------------------------------------------
% File     : NLP114-1 : TPTP v5.5.0. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 1
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "An old dirty white chevy barrels down a lonely street in
%            hollywood."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :   36 (  16 non-Horn;   2 unit;  36 RR)
%            Number of atoms       :  102 (   0 equality)
%            Maximal clause size   :   18 (   3 average)
%            Number of predicates  :   18 (   1 propositional; 0-3 arity)
%            Number of functors    :   11 (  11 constant; 0-0 arity)
%            Number of variables   :   11 (   0 singleton)
%            Maximal term depth    :    1 (   1 average)
% SPC      : CNF_SAT_EPR

% Comments : Created from NLP114+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    ( actual_world(skc17) )).

cnf(clause2,negated_conjecture,
    ( actual_world(skc11) )).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | city(skc17,skc20) )).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | street(skc17,skc20) )).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | lonely(skc17,skc20) )).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | placename(skc17,skc21) )).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc17,skc21) )).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | event(skc17,skc18) )).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | present(skc17,skc18) )).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | barrel(skc17,skc18) )).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | old(skc17,skc19) )).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | dirty(skc17,skc19) )).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | white(skc17,skc19) )).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | chevy(skc17,skc19) )).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc11,skc16) )).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | street(skc11,skc16) )).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc11,skc12) )).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | present(skc11,skc12) )).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | event(skc11,skc12) )).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc11,skc14) )).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc11,skc14) )).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | city(skc11,skc15) )).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc11,skc13) )).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | white(skc11,skc13) )).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc11,skc13) )).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | old(skc11,skc13) )).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | down(skc17,skc18,skc20) )).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | in(skc17,skc18,skc20) )).

cnf(clause29,negated_conjecture,
    ( ssSkC0
    | of(skc17,skc21,skc20) )).

cnf(clause30,negated_conjecture,
    ( ssSkC0
    | agent(skc17,skc18,skc19) )).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | down(skc11,skc12,skc16) )).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | in(skc11,skc12,skc15) )).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | of(skc11,skc14,skc15) )).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc11,skc12,skc13) )).

cnf(clause35,negated_conjecture,
    ( ~ down(U,V,W)
    | ~ lonely(U,W)
    | ~ street(U,W)
    | ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ hollywood_placename(U,X)
    | ~ placename(U,X)
    | ~ in(U,V,Y)
    | ~ city(U,Y)
    | ~ of(U,X,Y)
    | ~ chevy(U,Z)
    | ~ white(U,Z)
    | ~ dirty(U,Z)
    | ~ old(U,Z)
    | ~ agent(U,V,Z)
    | ~ actual_world(U)
    | ssSkC0 )).

cnf(clause36,negated_conjecture,
    ( ~ city(U,V)
    | ~ street(U,V)
    | ~ lonely(U,V)
    | ~ down(U,W,V)
    | ~ in(U,W,V)
    | ~ placename(U,X)
    | ~ hollywood_placename(U,X)
    | ~ of(U,X,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ barrel(U,W)
    | ~ agent(U,W,Y)
    | ~ old(U,Y)
    | ~ dirty(U,Y)
    | ~ white(U,Y)
    | ~ chevy(U,Y)
    | ~ actual_world(U)
    | ~ ssSkC0 )).

%--------------------------------------------------------------------------
