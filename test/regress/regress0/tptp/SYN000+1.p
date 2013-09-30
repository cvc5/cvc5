%------------------------------------------------------------------------------
% File     : SYN000+1 : TPTP v5.5.0. Released v4.0.0.
% Domain   : Syntactic
% Problem  : Basic TPTP FOF syntax
% Version  : Biased.
% English  : Basic TPTP FOF syntax that you can't survive without parsing.

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.43 v5.5.0, 0.48 v5.4.0, 0.46 v5.3.0, 0.52 v5.2.0, 0.40 v5.1.0, 0.43 v5.0.0, 0.54 v4.1.0, 0.57 v4.0.1, 0.78 v4.0.0
% Syntax   : Number of formulae    :   12 (   5 unit)
%            Number of atoms       :   31 (   3 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   28 (   9   ~;  10   |;   3   &)
%                                         (   1 <=>;   3  =>;   1  <=)
%                                         (   1 <~>;   0  ~|;   0  ~&)
%            Number of predicates  :   16 (  10 propositional; 0-3 arity)
%            Number of functors    :    8 (   5 constant; 0-3 arity)
%            Number of variables   :   13 (   0 sgn;   5   !;   8   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Propositional
fof(propositional,axiom,
    ( ( p0
      & ~ q0 )
   => ( r0
      | ~ s0 ) )).

%----First-order
fof(first_order,axiom,(
    ! [X] :
      ( ( p(X)
        | ~ q(X,a) )
     => ? [Y,Z] :
          ( r(X,f(Y),g(X,f(Y),Z))
          & ~ s(f(f(f(b)))) ) ) )).

%----Equality
fof(equality,axiom,(
    ? [Y] :
    ! [X,Z] :
      ( f(Y) = g(X,f(Y),Z)
      | f(f(f(b))) != a
      | X = f(Y) ) )).

%----True and false
fof(true_false,axiom,
    ( $true
    | $false )).

%----Quoted symbols
fof(single_quoted,axiom,
    ( 'A proposition'
    | 'A predicate'(a)
    | p('A constant')
    | p('A function'(a))
    | p('A \'quoted \\ escape\'') )).

%----Connectives - seen |, &, =>, ~ already
fof(useful_connectives,axiom,(
    ! [X] :
      ( ( p(X)
       <= ~ q(X,a) )
    <=> ? [Y,Z] :
          ( r(X,f(Y),g(X,f(Y),Z))
        <~> ~ s(f(f(f(b)))) ) ) )).

%----Annotated formula names
fof(123,axiom,(
    ! [X] :
      ( ( p(X)
        | ~ q(X,a) )
     => ? [Y,Z] :
          ( r(X,f(Y),g(X,f(Y),Z))
          & ~ s(f(f(f(b)))) ) ) )).

%----Roles
fof(role_hypothesis,hypothesis,(
    p(h) )).

fof(role_conjecture,conjecture,(
    ? [X] : p(X) )).

%----Include directive
include('Axioms/SYN000+0.ax').

%----Comments
/* This
   is a block
   comment.
*/

%------------------------------------------------------------------------------
