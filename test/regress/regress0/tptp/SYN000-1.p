%------------------------------------------------------------------------------
% File     : SYN000-1 : TPTP v5.5.0. Released v4.0.0.
% Domain   : Syntactic
% Problem  : Basic TPTP CNF syntax
% Version  : Biased.
% English  : Basic TPTP CNF syntax that you can't survive without parsing.

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.50 v5.4.0, 0.55 v5.3.0, 0.56 v5.2.0, 0.62 v5.1.0, 0.65 v5.0.0, 0.64 v4.1.0, 0.62 v4.0.1, 0.64 v4.0.0
% Syntax   : Number of clauses     :   11 (   6 non-Horn;   5 unit;   7 RR)
%            Number of atoms       :   27 (   3 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   16 (  10 propositional; 0-3 arity)
%            Number of functors    :    8 (   5 constant; 0-3 arity)
%            Number of variables   :   11 (   5 singleton)
%            Maximal term depth    :    4 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%------------------------------------------------------------------------------
%----Propositional
cnf(propositional,axiom,
    ( p0
    | ~ q0
    | r0
    | ~ s0 )).

%----First-order
cnf(first_order,axiom,
    ( p(X)
    | ~ q(X,a)
    | r(X,f(Y),g(X,f(Y),Z))
    | ~ s(f(f(f(b)))) )).

%----Equality
cnf(equality,axiom,
    ( f(Y) = g(X,f(Y),Z)
    | f(f(f(b))) != a
    | X = f(Y) )).

%----True and false
cnf(true_false,axiom,
    ( $true
    | $false )).

%----Quoted symbols
cnf(single_quoted,axiom,
    ( 'A proposition'
    | 'A predicate'(Y)
    | p('A constant')
    | p('A function'(a))
    | p('A \'quoted \\ escape\'') )).

%----Connectives - seen them all already

%----Annotated formula names
cnf(123,axiom,
    ( p(X)
    | ~ q(X,a)
    | r(X,f(Y),g(X,f(Y),Z))
    | ~ s(f(f(f(b)))) )).

%----Roles - seen axiom already
cnf(role_hypothesis,hypothesis,
    p(h)).

cnf(role_negated_conjecture,negated_conjecture,
    ~ p(X)).

%----Include directive
include('Axioms/SYN000-0.ax').

%----Comments
/* This
   is a block
   comment.
*/

%------------------------------------------------------------------------------
