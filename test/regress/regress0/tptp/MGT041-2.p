%--------------------------------------------------------------------------
% File     : MGT041-2 : TPTP v5.5.0. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : There are non-FM and non-EP organisations
% Version  : [PM93] axioms.
% English  : There are non-first mover and non-efficient producers
%            organisations.

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :    8 (   1 non-Horn;   4 unit;   8 RR)
%            Number of atoms       :   17 (   0 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   4 constant; 0-0 arity)
%            Number of variables   :    8 (   1 singleton)
%            Maximal term depth    :    1 (   1 average)
% SPC      : CNF_UNS_EPR

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT041+2.p
%--------------------------------------------------------------------------
cnf(mp_not_high_and_low_1,axiom,
    ( ~ number_of_routines(A,B,low)
    | ~ number_of_routines(A,B,high) )).

cnf(a14_2,hypothesis,
    ( ~ organisation_at_time(A,B)
    | ~ efficient_producer(A)
    | ~ founding_time(A,B)
    | has_elaborated_routines(A,B) )).

cnf(a15_3,hypothesis,
    ( ~ organisation_at_time(A,B)
    | ~ first_mover(A)
    | ~ founding_time(A,B)
    | number_of_routines(A,B,low) )).

cnf(a16_4,hypothesis,
    ( organisation_at_time(sk1,sk2) )).

cnf(a16_5,hypothesis,
    ( founding_time(sk1,sk2) )).

cnf(a16_6,hypothesis,
    ( number_of_routines(sk1,sk2,high) )).

cnf(a16_7,hypothesis,
    ( ~ has_elaborated_routines(sk1,sk2) )).

cnf(prove_t10_8,negated_conjecture,
    ( ~ organisation_at_time(A,B)
    | first_mover(A)
    | efficient_producer(A) )).

%--------------------------------------------------------------------------
