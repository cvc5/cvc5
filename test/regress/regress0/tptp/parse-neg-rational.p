%------------------------------------------------------------------------------
% File     : ARI196=1 : TPTP v7.4.0. Released v5.0.0.
% Domain   : Arithmetic
% Problem  : Rational: -1/4 less than 1/4
% Version  : Especial.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.2.0, 0.20 v6.1.0, 0.22 v6.0.0, 0.25 v5.3.0, 0.14 v5.2.0, 0.20 v5.1.0, 0.25 v5.0.0
% Syntax   : Number of formulae    :    1 (   1 unit;   0 type)
%            Number of atoms       :    1 (   0 equality)
%            Maximal formula depth :    1 (   1 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   2 constant; 0-0 arity)
%            Number of variables   :    0 (   0 sgn;   0   !;   0   ?)
%                                         (   0   :;   0  !>;   0  ?*)
%            Maximal term depth    :    1 (   1 average)
%            Arithmetic symbols    :    2 (   1 prd;   0 fun;   1 num;   0 var)
% SPC      : TF0_THM_NEQ_ARI

% Comments :
%------------------------------------------------------------------------------
tff(rat_less_problem_7,conjecture,(
    $less(-1/4,1/4) )).
%------------------------------------------------------------------------------
