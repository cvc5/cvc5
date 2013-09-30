%--------------------------------------------------------------------------
% File     : MGT031-1 : TPTP v5.5.0. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : First movers appear first in an environment
% Version  : [PB+94] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v2.5.0, 0.17 v2.4.0
% Syntax   : Number of clauses     :   15 (   2 non-Horn;   3 unit;  15 RR)
%            Number of atoms       :   38 (   5 equality)
%            Maximal clause size   :    5 (   3 average)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :   10 (   6 constant; 0-2 arity)
%            Number of variables   :   23 (   0 singleton)
%            Maximal term depth    :    3 (   1 average)
% SPC      : CNF_SAT_RFO_EQU_NUE

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT031+1.p
%--------------------------------------------------------------------------
cnf(mp_positive_number_when_appear_20,axiom,
    ( ~ environment(A)
    | greater(number_of_organizations(e,appear(an_organisation,A)),zero) )).

cnf(mp_number_mean_non_empty_21,axiom,
    ( ~ environment(A)
    | ~ greater(number_of_organizations(A,B),zero)
    | subpopulation(sk1(B,A),A,B) )).

cnf(mp_number_mean_non_empty_22,axiom,
    ( ~ environment(A)
    | ~ greater(number_of_organizations(A,B),zero)
    | greater(cardinality_at_time(sk1(B,A),B),zero) )).

cnf(mp_no_EP_before_appearance_23,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | ~ greater(appear(efficient_producers,A),B)
    | ~ greater(cardinality_at_time(efficient_producers,B),zero) )).

cnf(mp_no_FM_before_appearance_24,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | ~ greater(appear(first_movers,A),B)
    | ~ greater(cardinality_at_time(first_movers,B),zero) )).

cnf(mp_FM_not_precede_first_25,axiom,
    ( ~ environment(A)
    | greater_or_equal(appear(first_movers,A),appear(an_organisation,A)) )).

cnf(mp_greater_transitivity_26,axiom,
    ( ~ greater(A,B)
    | ~ greater(B,C)
    | greater(A,C) )).

cnf(mp_greater_or_equal_27,axiom,
    ( ~ greater_or_equal(A,B)
    | greater(A,B)
    | A = B )).

cnf(mp_greater_or_equal_28,axiom,
    ( ~ greater(A,B)
    | greater_or_equal(A,B) )).

cnf(mp_greater_or_equal_29,axiom,
    ( A != B
    | greater_or_equal(A,B) )).

cnf(a9_30,hypothesis,
    ( ~ environment(A)
    | ~ subpopulation(B,A,C)
    | ~ greater(cardinality_at_time(B,C),zero)
    | B = efficient_producers
    | B = first_movers )).

cnf(a13_31,hypothesis,
    ( ~ environment(A)
    | greater(appear(efficient_producers,e),appear(first_movers,A)) )).

cnf(prove_l13_32,negated_conjecture,
    ( environment(sk2) )).

cnf(prove_l13_33,negated_conjecture,
    ( in_environment(sk2,appear(an_organisation,sk2)) )).

cnf(prove_l13_34,negated_conjecture,
    (  appear(an_organisation,sk2) != appear(first_movers,sk2) )).

%--------------------------------------------------------------------------
