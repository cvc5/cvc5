%--------------------------------------------------------------------------
% File     : BOO003-4 : TPTP v5.5.0. Released v1.1.0.
% Domain   : Boolean Algebra
% Problem  : Multiplication is idempotent (X * X = X)
% Version  : [Ver94] (equality) axioms.
% English  :

% Refs     : [Ver94] Veroff (1994), Problem Set
% Source   : [Ver94]
% Names    : TA [Ver94]

% Status   : Unsatisfiable
% Rating   : 0.10 v5.5.0, 0.05 v5.4.0, 0.00 v2.1.0, 0.13 v2.0.0
% Syntax   : Number of clauses     :    9 (   0 non-Horn;   9 unit;   1 RR)
%            Number of atoms       :    9 (   9 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    6 (   3 constant; 0-2 arity)
%            Number of variables   :   14 (   0 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Include boolean algebra axioms for equality formulation
include('Axioms/BOO004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_a_times_a_is_a,negated_conjecture,
    (  multiply(a,a) != a )).

%--------------------------------------------------------------------------
