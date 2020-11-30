% COMMAND-LINE: --no-finite-model-find
%------------------------------------------------------------------------------
% File     : DAT001=1 : TPTP v5.5.0. Released v5.0.0.
% Domain   : Data Structures
% Problem  : Recursive list sort
% Version  : Especial.
% English  : 

% Refs     : 
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.12 v5.5.0, 0.25 v5.4.0, 0.38 v5.3.0, 0.29 v5.2.0, 0.20 v5.1.0, 0.25 v5.0.0
% Syntax   : Number of formulae    :    8 (   5 unit;   4 type)
%            Number of atoms       :   13 (   0 equality)
%            Maximal formula depth :    6 (   3 average)
%            Number of connectives :    2 (   0   ~;   0   |;   1   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    3 (   2   >;   1   *;   0   +;   0  <<)
%            Number of predicates  :    9 (   7 propositional; 0-2 arity)
%            Number of functors    :    7 (   6 constant; 0-2 arity)
%            Number of variables   :    4 (   0 sgn;   4   !;   0   ?)
%            Maximal term depth    :    6 (   2 average)
%            Arithmetic symbols    :    7 (   2 pred;    0 func;    5 numbers)
% SPC      : TFF_THM_NEQ_ARI

% Comments :
%------------------------------------------------------------------------------
tff(list_type,type,(
    list: $tType )).

tff(nil_type,type,(
    nil: list )).

tff(mycons_type,type,(
    mycons: ( $int * list ) > list )).

tff(sorted_type,type,(
    sorted: list > $o )).

tff(empty_is_sorted,axiom,(
    sorted(nil) )).

tff(single_is_sorted,axiom,(
    ! [X: $int] : sorted(mycons(X,nil)) )).

tff(recursive_sort,axiom,(
    ! [X: $int,Y: $int,R: list] :
      ( ( $less(X,Y)
        & sorted(mycons(Y,R)) )
     => sorted(mycons(X,mycons(Y,R))) ) )).

tff(check_list,conjecture,(
    sorted(mycons(1,mycons(2,mycons(4,mycons(7,mycons(100,nil)))))) )).

%------------------------------------------------------------------------------
